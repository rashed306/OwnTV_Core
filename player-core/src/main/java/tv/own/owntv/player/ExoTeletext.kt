package tv.own.owntv.player

import android.graphics.Color
import android.net.Uri
import android.text.SpannableStringBuilder
import android.text.Spanned
import android.text.style.ForegroundColorSpan
import android.util.SparseArray
import androidx.annotation.OptIn
import androidx.media3.common.C
import androidx.media3.common.Format
import androidx.media3.common.MimeTypes
import androidx.media3.common.text.Cue
import androidx.media3.common.util.ParsableByteArray
import androidx.media3.common.util.TimestampAdjuster
import androidx.media3.common.util.UnstableApi
import androidx.media3.extractor.Extractor
import androidx.media3.extractor.ExtractorOutput
import androidx.media3.extractor.ExtractorsFactory
import androidx.media3.extractor.TrackOutput
import androidx.media3.extractor.text.CueEncoder
import androidx.media3.extractor.text.DefaultSubtitleParserFactory
import androidx.media3.extractor.text.SubtitleParser
import androidx.media3.extractor.ts.DefaultTsPayloadReaderFactory
import androidx.media3.extractor.ts.ElementaryStreamReader
import androidx.media3.extractor.ts.PesReader
import androidx.media3.extractor.ts.TsExtractor
import androidx.media3.extractor.ts.TsPayloadReader
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.asStateFlow

/**
 * OwnTVnew: subtitle timing for the ExoPlayer live engine. Every subtitle sample is re-stamped as it
 * is read from the stream: positive = later, negative = earlier. Earlier only works as far as the
 * stream has been read ahead of the picture; the app pauses briefly to read further when needed.
 */
object SubtitleTimeShift {
    private val _offsetMs = MutableStateFlow(0)
    val offsetMs: StateFlow<Int> = _offsetMs.asStateFlow()

    @Volatile internal var offsetUs: Long = 0L
        private set

    fun set(ms: Int) {
        _offsetMs.value = ms
        offsetUs = ms * MS_US
    }

    private const val MS_US = 1000L
}

/**
 * OwnTVnew: the TS extractor ExoPlayer uses for raw MPEG-TS, plus DVB teletext subtitles (which
 * Media3 drops) and the [SubtitleTimeShift] re-stamping. Everything else is the stock factory's.
 */
@OptIn(UnstableApi::class)
internal class OwnTvExtractorsFactory(
    private val base: androidx.media3.extractor.DefaultExtractorsFactory,
    private val tsFlags: Int,
    private val tsSubtitleFormats: List<Format>,
) : ExtractorsFactory {
    private var parserFactory: SubtitleParser.Factory = DefaultSubtitleParserFactory()
    private var transcoding = true

    override fun experimentalSetTextTrackTranscodingEnabled(enabled: Boolean): ExtractorsFactory {
        transcoding = enabled
        base.experimentalSetTextTrackTranscodingEnabled(enabled)
        return this
    }

    override fun setSubtitleParserFactory(subtitleParserFactory: SubtitleParser.Factory): ExtractorsFactory {
        parserFactory = subtitleParserFactory
        base.setSubtitleParserFactory(subtitleParserFactory)
        return this
    }

    override fun createExtractors(): Array<Extractor> = adapt(base.createExtractors())

    override fun createExtractors(uri: Uri, responseHeaders: Map<String, List<String>>): Array<Extractor> =
        adapt(base.createExtractors(uri, responseHeaders))

    private fun adapt(list: Array<Extractor>): Array<Extractor> = list.map { e ->
        val x = if (e is TsExtractor) {
            TsExtractor(
                TsExtractor.MODE_SINGLE_PMT,
                if (transcoding) 0 else TsExtractor.FLAG_EMIT_RAW_SUBTITLE_DATA,
                parserFactory,
                TimestampAdjuster(0),
                TeletextPayloadReaderFactory(DefaultTsPayloadReaderFactory(tsFlags, tsSubtitleFormats)),
                TsExtractor.DEFAULT_TIMESTAMP_SEARCH_BYTES,
            )
        } else {
            e
        }
        ShiftingExtractor(x)
    }.toTypedArray()
}

/** Passes everything through, re-stamping text samples by [SubtitleTimeShift]. */
@OptIn(UnstableApi::class)
private class ShiftingExtractor(private val inner: Extractor) : Extractor by inner {
    override fun init(output: ExtractorOutput) = inner.init(ShiftingOutput(output))
    override fun getUnderlyingImplementation(): Extractor = inner.underlyingImplementation
}

@OptIn(UnstableApi::class)
private class ShiftingOutput(private val inner: ExtractorOutput) : ExtractorOutput by inner {
    override fun track(id: Int, type: Int): TrackOutput {
        val t = inner.track(id, type)
        return if (type == C.TRACK_TYPE_TEXT) ShiftingTrack(t) else t
    }
}

@OptIn(UnstableApi::class)
private class ShiftingTrack(private val inner: TrackOutput) : TrackOutput by inner {
    override fun sampleMetadata(timeUs: Long, flags: Int, size: Int, offset: Int, cryptoData: TrackOutput.CryptoData?) {
        val shifted = if (timeUs == C.TIME_UNSET) timeUs else maxOf(0L, timeUs + SubtitleTimeShift.offsetUs)
        inner.sampleMetadata(shifted, flags, size, offset, cryptoData)
    }
}

/** Stock payload readers, plus DVB teletext (PES private data with a teletext descriptor). */
@OptIn(UnstableApi::class)
private class TeletextPayloadReaderFactory(private val base: DefaultTsPayloadReaderFactory) : TsPayloadReader.Factory {
    override fun createInitialPayloadReaders(): SparseArray<TsPayloadReader> = base.createInitialPayloadReaders()

    override fun createPayloadReader(streamType: Int, esInfo: TsPayloadReader.EsInfo): TsPayloadReader? {
        base.createPayloadReader(streamType, esInfo)?.let { return it }
        val pages = teletextPages(esInfo.descriptorBytes)
        return if (pages.isEmpty()) null else PesReader(TeletextReader(pages))
    }

    /** Subtitle pages (types 2 and 5) of a teletext descriptor (tag 0x56), with their languages. */
    private fun teletextPages(d: ByteArray): List<TeletextPageInfo> {
        val out = ArrayList<TeletextPageInfo>()
        var i = 0
        while (i + 2 <= d.size) {
            val tag = d[i].toInt() and 0xFF
            val len = d[i + 1].toInt() and 0xFF
            val end = minOf(d.size, i + 2 + len)
            if (tag == TELETEXT_DESCRIPTOR) {
                var p = i + 2
                while (p + 5 <= end) {
                    val lang = String(d, p, 3, Charsets.ISO_8859_1).trim()
                    val b = d[p + 3].toInt() and 0xFF
                    val type = b shr 3
                    val mag = (b and 7).let { if (it == 0) 8 else it }
                    val page = d[p + 4].toInt() and 0xFF
                    if (type == TYPE_SUBTITLE || type == TYPE_SUBTITLE_HOH) out += TeletextPageInfo(lang, mag, page)
                    p += 5
                }
            }
            i = end
        }
        return out.distinct()
    }

    private companion object {
        const val TELETEXT_DESCRIPTOR = 0x56
        const val TYPE_SUBTITLE = 2
        const val TYPE_SUBTITLE_HOH = 5
    }
}

/** One subtitle page: magazine 1–8 and page number in BCD (e.g. 0x88 for page 888). */
internal data class TeletextPageInfo(val lang: String, val magazine: Int, val pageBcd: Int)

/**
 * Decodes EBU teletext (ETSI EN 300 472 / ETS 300 706) subtitle pages from the PES payload and writes
 * each page update as a Media3 cues sample — one track per language page, replacing what was shown.
 */
@OptIn(UnstableApi::class)
private class TeletextReader(private val pages: List<TeletextPageInfo>) : ElementaryStreamReader {
    private val outputs = arrayOfNulls<TrackOutput>(pages.size)
    private val decoders = pages.map { TeletextPageDecoder(it) }
    private var timeUs = C.TIME_UNSET
    private val pes = java.io.ByteArrayOutputStream()
    private val encoder = CueEncoder()

    // A "clear" is held until the line has been up for a reading time (a new line replaces it at
    // once): broadcasters often clear a teletext subtitle sooner than it can be read.
    private val shownAtUs = LongArray(pages.size) { C.TIME_UNSET }
    private val shownChars = IntArray(pages.size)
    private val clearPending = BooleanArray(pages.size)

    override fun seek() {
        pes.reset()
        timeUs = C.TIME_UNSET
        decoders.forEach { it.reset() }
        shownAtUs.fill(C.TIME_UNSET); clearPending.fill(false)
    }

    override fun createTracks(extractorOutput: ExtractorOutput, idGenerator: TsPayloadReader.TrackIdGenerator) {
        for (i in pages.indices) {
            idGenerator.generateNewId()
            val out = extractorOutput.track(idGenerator.trackId, C.TRACK_TYPE_TEXT)
            out.format(
                Format.Builder()
                    .setId(idGenerator.formatId)
                    .setSampleMimeType(MimeTypes.APPLICATION_MEDIA3_CUES)
                    .setCodecs(CODEC_LABEL)
                    .setCueReplacementBehavior(Format.CUE_REPLACEMENT_BEHAVIOR_REPLACE)
                    .setLanguage(pages[i].lang.ifEmpty { null })
                    .build(),
            )
            outputs[i] = out
        }
    }

    override fun packetStarted(pesTimeUs: Long, flags: Int) {
        pes.reset()
        timeUs = pesTimeUs
    }

    override fun consume(data: ParsableByteArray) {
        pes.write(data.data, data.position, data.bytesLeft())
        data.skipBytes(data.bytesLeft())
    }

    override fun packetFinished() {
        val buf = pes.toByteArray()
        pes.reset()
        if (buf.isEmpty() || timeUs == C.TIME_UNSET) return
        // data_identifier 0x10–0x1F, then data units: id, length (44), field byte, framing code, 42 bytes.
        if ((buf[0].toInt() and 0xFF) !in DATA_ID_MIN..DATA_ID_MAX) return
        var p = 1
        while (p + 2 <= buf.size) {
            val unitId = buf[p].toInt() and 0xFF
            val len = buf[p + 1].toInt() and 0xFF
            if (p + 2 + len > buf.size) break
            if ((unitId == UNIT_SUBTITLE || unitId == UNIT_NON_SUBTITLE) && len >= UNIT_LEN) {
                val packet = ByteArray(PACKET_LEN) { k -> reverse(buf[p + 4 + k]) }
                for (i in decoders.indices) {
                    decoders[i].packet(packet)?.let { cues -> onPage(i, cues) }
                }
            }
            p += 2 + len
        }
        flushClears()
    }

    private fun onPage(i: Int, cues: List<Cue>) {
        if (cues.isEmpty()) {
            clearPending[i] = true
            return
        }
        clearPending[i] = false
        write(i, cues, timeUs)
        shownAtUs[i] = timeUs
        shownChars[i] = cues.sumOf { it.text?.length ?: 0 }
    }

    /** Clears whose line has now been up long enough, stamped when its reading time ran out. */
    private fun flushClears() {
        for (i in clearPending.indices) {
            if (!clearPending[i]) continue
            val since = shownAtUs[i]
            val deadline = if (since == C.TIME_UNSET) timeUs else since + readingUs(shownChars[i])
            if (timeUs < deadline) continue
            clearPending[i] = false
            write(i, emptyList(), deadline)
            shownAtUs[i] = C.TIME_UNSET
        }
    }

    private fun write(i: Int, cues: List<Cue>, atUs: Long) {
        val out = outputs[i] ?: return
        val bytes = encoder.encode(cues, C.TIME_UNSET)
        out.sampleData(ParsableByteArray(bytes), bytes.size)
        out.sampleMetadata(atUs, C.BUFFER_FLAG_KEY_FRAME, bytes.size, 0, null)
    }

    /** 2.5 s for a short line up to 7 s for a long one (as the mpv overlay does). */
    private fun readingUs(chars: Int): Long = (MIN_READ_US + PER_CHAR_US * chars).coerceAtMost(MAX_READ_US)

    private companion object {
        const val CODEC_LABEL = "teletext"
        const val DATA_ID_MIN = 0x10
        const val DATA_ID_MAX = 0x1F
        const val UNIT_NON_SUBTITLE = 0x02
        const val UNIT_SUBTITLE = 0x03
        const val UNIT_LEN = 44
        const val PACKET_LEN = 42
        const val MIN_READ_US = 2_500_000L
        const val MAX_READ_US = 7_000_000L
        const val PER_CHAR_US = 60_000L

        fun reverse(b: Byte): Byte = (Integer.reverse(b.toInt() and 0xFF) ushr 24).toByte()
    }
}

/**
 * One teletext subtitle page being received. [packet] takes one 42-byte packet (MRAG + 40 bytes) and
 * returns the page's cues when a transmission of it completes and differs from what is shown.
 */
@OptIn(UnstableApi::class)
private class TeletextPageDecoder(private val info: TeletextPageInfo) {
    private val rows = arrayOfNulls<ByteArray>(ROWS)
    private var receiving = false
    private var charset = 0
    private var shown: List<String> = emptyList()

    fun reset() {
        rows.fill(null); receiving = false; shown = emptyList()
    }

    fun packet(pk: ByteArray): List<Cue>? {
        val a = ham(pk[0]); val b = ham(pk[1])
        if (a < 0 || b < 0) return null
        val mag = (a and 7).let { if (it == 0) 8 else it }
        val row = (a shr 3) or (b shl 1)
        if (row == 0) {
            // A header ends the page this magazine was sending (parallel mode), so finish ours first.
            val done = if (receiving && mag == info.magazine) finish() else null
            val units = ham(pk[2]); val tens = ham(pk[3])
            val s2 = ham(pk[5]); val c11 = ham(pk[9])
            if (units < 0 || tens < 0) return done
            val page = (tens shl 4) or units
            if (mag == info.magazine && page == info.pageBcd) {
                receiving = true
                if (s2 >= 0 && (s2 and 8) != 0) rows.fill(null) // C4: erase page
                if (c11 >= 0) charset = (c11 shr 1) and 7
            } else if (mag == info.magazine) {
                receiving = false
            }
            return done
        }
        if (receiving && mag == info.magazine && row in 1 until ROWS) {
            rows[row] = pk.copyOfRange(2, 42)
        }
        return null
    }

    /** The page as cues, or null when it shows what is already on screen. */
    private fun finish(): List<Cue>? {
        receiving = false
        val lines = ArrayList<Pair<CharSequence, String>>()
        var firstRow = -1
        for (r in 1 until ROWS) {
            val bytes = rows[r] ?: continue
            val line = decodeRow(bytes) ?: continue
            if (firstRow < 0) firstRow = r
            lines += line
        }
        val plain = lines.map { it.second }
        if (plain == shown) return null
        shown = plain
        if (lines.isEmpty()) return emptyList()
        val text = SpannableStringBuilder()
        lines.forEachIndexed { i, (styled, _) -> if (i > 0) text.append('\n'); text.append(styled) }
        val b = Cue.Builder().setText(text).setTextAlignment(android.text.Layout.Alignment.ALIGN_CENTER)
        if (firstRow in 1..TOP_HALF_LAST_ROW) b.setLine(TOP_LINE, Cue.LINE_TYPE_FRACTION).setLineAnchor(Cue.ANCHOR_TYPE_START)
        return listOf(b.build())
    }

    /** One row's visible text with its colours, or null when it is blank. */
    private fun decodeRow(bytes: ByteArray): Pair<CharSequence, String>? {
        val out = SpannableStringBuilder()
        var color = Color.WHITE
        var mosaic = false
        var spanStart = 0
        var spanColor = color
        for (raw in bytes) {
            val c = raw.toInt() and 0x7F
            if (c < 0x20) {
                when (c) {
                    in 0x00..0x07 -> { color = ALPHA_COLORS[c]; mosaic = false }
                    in 0x10..0x17 -> mosaic = true
                }
                out.append(' ')
                continue
            }
            if (color != spanColor) {
                if (out.length > spanStart) out.setSpan(ForegroundColorSpan(spanColor), spanStart, out.length, Spanned.SPAN_EXCLUSIVE_EXCLUSIVE)
                spanStart = out.length; spanColor = color
            }
            out.append(if (mosaic) ' ' else char(c))
        }
        if (out.length > spanStart) out.setSpan(ForegroundColorSpan(spanColor), spanStart, out.length, Spanned.SPAN_EXCLUSIVE_EXCLUSIVE)
        val plain = out.toString().trim()
        if (plain.isEmpty()) return null
        // Trim the styled copy the same way, keeping its colour spans.
        val start = out.indexOfFirst { !it.isWhitespace() }
        val end = out.indexOfLast { !it.isWhitespace() } + 1
        return out.subSequence(start, end) to plain
    }

    private fun char(c: Int): Char {
        val i = NATIONAL_POSITIONS.indexOf(c)
        if (i >= 0) NATIONAL[charset]?.let { return it[i] }
        return if (c == 0x7F) ' ' else c.toChar()
    }

    private companion object {
        const val ROWS = 25
        const val TOP_HALF_LAST_ROW = 11
        const val TOP_LINE = 0.1f

        val ALPHA_COLORS = intArrayOf(
            Color.BLACK, Color.RED, Color.GREEN, Color.YELLOW, Color.BLUE, Color.MAGENTA, Color.CYAN, Color.WHITE,
        )

        // G0 Latin national option sub-sets (ETS 300 706 table 36), by C12–C14.
        val NATIONAL_POSITIONS = intArrayOf(0x23, 0x24, 0x40, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60, 0x7B, 0x7C, 0x7D, 0x7E)
        val NATIONAL: Array<String?> = arrayOf(
            "£\$@←½→↑#–¼‖¾÷", // English
            "#\$§ÄÖÜ^_°äöüß", // German
            "#¤ÉÄÖÅÜ_éäöåü", // Swedish / Finnish
            "£\$é°ç→↑#ùàòèì", // Italian
            "éïàëêùî#èâôûç", // French
            "ç\$¡áéíóú¿üñèà", // Portuguese / Spanish
            null, null,
        )

        /** Hamming 8/4: the four data bits (1, 3, 5, 7), or -1. Single-bit errors are not corrected. */
        fun ham(b: Byte): Int {
            val v = b.toInt() and 0xFF
            return ((v shr 1) and 1) or (((v shr 3) and 1) shl 1) or (((v shr 5) and 1) shl 2) or (((v shr 7) and 1) shl 3)
        }
    }
}
