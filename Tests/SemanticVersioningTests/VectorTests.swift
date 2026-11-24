import Foundation
import Testing

@testable import SemanticVersioning

/// Lean の参照パーサと実装モデルから生成したベクタ(`Vectors/`)との突き合わせ。
///
/// ベクタは `Formal/` で `lake exe vectors ../Tests/SemanticVersioningTests/Vectors` を実行して作る。
/// 生成元の定義は仕様との一致が証明されているので、ここで食い違えば Swift 側の誤りである。
@Suite("Lean から生成したベクタとの一致")
struct VectorTests {
    private static func lines(of name: String) throws -> [Substring] {
        let url = try #require(
            Bundle.module.url(forResource: name, withExtension: "txt", subdirectory: "Vectors"))
        let text = try String(contentsOf: url, encoding: .utf8)
        return text.split(separator: "\n").filter { !$0.hasPrefix("#") }
    }

    @Test("256 個のバイトすべてで文字クラスが一致する")
    func byteClasses() throws {
        let rows = try Self.lines(of: "byte-classes")
        #expect(rows.count == 256)
        var mismatches: [String] = []
        for row in rows {
            let fields = row.split(separator: " ")
            let byte = try #require(UInt8(fields[0], radix: 16))
            var flags = ""
            if Grammar.isPositiveDigit(byte) { flags += "p" }
            if Grammar.isDigit(byte) { flags += "d" }
            if Grammar.isLetter(byte) { flags += "l" }
            if Grammar.isNonDigit(byte) { flags += "n" }
            if Grammar.isIdentifierCharacter(byte) { flags += "i" }
            if flags.isEmpty { flags = "-" }
            if flags != fields[1] {
                mismatches.append("\(fields[0]): expected \(fields[1]), got \(flags)")
            }
        }
        #expect(mismatches.isEmpty, "\(mismatches)")
    }

    /// 接頭辞の後ろに `extra` 文字まで続けた文字列を全数列挙し、妥当性の判定が一覧と一致することを確かめる。
    private struct Enumeration {
        let alphabet: [UInt8]
        let valid: Set<[UInt8]>
        var checked = 0
        var accepted = 0
        var mismatches: [String] = []

        mutating func visit(_ buffer: [UInt8]) {
            checked += 1
            let version = SemanticVersion(utf8: buffer)
            let expected = valid.contains(buffer)
            if version != nil {
                accepted += 1
            }
            let roundTrips = version.map { Array($0.description.utf8) == buffer } ?? true
            if (version != nil) != expected || !roundTrips {
                if mismatches.count < 20 {
                    mismatches.append(String(decoding: buffer, as: UTF8.self))
                }
            }
        }

        mutating func run(_ buffer: inout [UInt8], extra: Int) {
            visit(buffer)
            guard extra > 0 else {
                return
            }
            for byte in alphabet {
                buffer.append(byte)
                run(&buffer, extra: extra - 1)
                buffer.removeLast()
            }
        }
    }

    @Test("全数列挙した文字列について、妥当性の判定が一致する")
    func grammar() throws {
        let rows = try Self.lines(of: "grammar")
        let header = try #require(rows.first)
        #expect(header.hasPrefix("alphabet "))
        let alphabet = try header.split(separator: " ").dropFirst().map {
            try #require(UInt8($0, radix: 16))
        }
        #expect(alphabet.count == 7)

        // 区間ごとに (接頭辞, 追加文字数, 妥当な文字列の集合) を読む。
        var sections: [(prefix: [UInt8], extra: Int, valid: Set<[UInt8]>)] = []
        for row in rows.dropFirst() {
            if row.hasPrefix("section") {
                let fields = row.split(separator: " ")
                let extra = try #require(Int(fields[1]))
                let prefix = fields.count > 2 ? Array(fields[2].utf8) : []
                sections.append((prefix, extra, []))
            } else {
                try #require(!sections.isEmpty)
                sections[sections.count - 1].valid.insert(Array(row.utf8))
            }
        }
        #expect(sections.count == 5)

        var totalChecked = 0
        for section in sections {
            var enumeration = Enumeration(alphabet: alphabet, valid: section.valid)
            var buffer = section.prefix
            enumeration.run(&buffer, extra: section.extra)
            let name = String(decoding: section.prefix, as: UTF8.self)
            #expect(enumeration.mismatches.isEmpty, "prefix \"\(name)\": \(enumeration.mismatches)")
            // 一覧のすべての文字列が列挙範囲に入っていて、かつ受理されたこと。
            #expect(enumeration.accepted == section.valid.count, "prefix \"\(name)\"")
            totalChecked += enumeration.checked
        }
        // 7 文字以下の全数 (7^8 - 1) / 6 = 960,800 件と、接頭辞つきの 4 区間。
        #expect(totalChecked == 960_800 + 19_608 + 3 * 2_801)
    }

    @Test("見本のすべての組について、優先順位が一致する")
    func precedence() throws {
        let rows = try Self.lines(of: "precedence")
        // 1 行が優先順位の等しい 1 組で、行は優先順位の昇順に並んでいる。
        var versions: [(rank: Int, version: SemanticVersion, string: Substring)] = []
        for (rank, row) in rows.enumerated() {
            for string in row.split(separator: " ") {
                let version = try #require(SemanticVersion(String(string)))
                #expect(version.description == string)
                versions.append((rank, version, string))
            }
        }
        #expect(versions.count > 1_000)

        var mismatches: [String] = []
        for a in versions {
            for b in versions {
                let ok =
                    (a.version < b.version) == (a.rank < b.rank)
                    && (a.version == b.version) == (a.rank == b.rank)
                    && (a.version > b.version) == (a.rank > b.rank)
                    && (a.rank != b.rank || a.version.hashValue == b.version.hashValue)
                if !ok && mismatches.count < 20 {
                    mismatches.append("\(a.string) vs \(b.string)")
                }
            }
        }
        #expect(mismatches.isEmpty, "\(mismatches)")

        // 標準ライブラリの整列でも同じ並びになる。
        let sorted = versions.shuffled().sorted { $0.version < $1.version }
        #expect(sorted.map(\.rank) == versions.map(\.rank))
    }
}
