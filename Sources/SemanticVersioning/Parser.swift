// バージョン文字列と構成要素の相互変換。
//
// Formal/SemVer/Parser/ の参照パーサを写したもの。参照パーサは BNF と同値であること
// (`validSemVer_iff_parse`)と、`parse` と `render` が互いに逆であること
// (`parse_sound`, `parse_complete`)が証明されている。

enum Parser {
    // MARK: 分割

    /// 最初の区切りバイトの前と後ろに分ける。区切りバイトがなければ後ろは `nil`。
    ///
    /// Lean: `SemVer.splitFirst`
    static func splitFirst(
        _ sep: UInt8, _ s: ArraySlice<UInt8>
    ) -> (ArraySlice<UInt8>, ArraySlice<UInt8>?) {
        guard let i = s.firstIndex(of: sep) else {
            return (s, nil)
        }
        return (s[s.startIndex..<i], s[(i + 1)..<s.endIndex])
    }

    /// すべての区切りバイトで分割する。結果は必ず 1 個以上の区間を持つ。
    ///
    /// Lean: `SemVer.splitOn`(先頭の区間と残りの区間の組を、1 本の配列として返す)
    static func splitOn(_ sep: UInt8, _ s: ArraySlice<UInt8>) -> [ArraySlice<UInt8>] {
        var parts: [ArraySlice<UInt8>] = []
        var start = s.startIndex
        for i in s.indices where s[i] == sep {
            parts.append(s[start..<i])
            start = i + 1
        }
        parts.append(s[start..<s.endIndex])
        return parts
    }

    // MARK: 文字列から構成要素へ

    /// `-` または `+` の後ろをドットで識別子に分ける。その部分がなければ空列。
    ///
    /// Lean: `SemVer.parseIdentifiers`
    static func parseIdentifiers(_ s: ArraySlice<UInt8>?) -> [[UInt8]] {
        guard let s else {
            return []
        }
        return splitOn(Ascii.dot, s).map { Array($0) }
    }

    /// コア部分をドットで 3 つに分け、構成要素を組み立てる。ちょうど 3 つでなければ失敗する。
    ///
    /// Lean: `SemVer.assemble`
    static func assemble(
        _ core: ArraySlice<UInt8>, _ pre: ArraySlice<UInt8>?, _ build: ArraySlice<UInt8>?
    ) -> Components? {
        let parts = splitOn(Ascii.dot, core)
        guard parts.count == 3 else {
            return nil
        }
        return Components(
            major: Array(parts[0]),
            minor: Array(parts[1]),
            patch: Array(parts[2]),
            preRelease: parseIdentifiers(pre),
            build: parseIdentifiers(build)
        )
    }

    /// 識別子の中身を検査せずに分解する。
    /// 最初の `+` でビルドメタデータを切り離し、残りを最初の `-` でコアとプレリリースに分ける。
    ///
    /// Lean: `SemVer.decompose`
    static func decompose(_ s: ArraySlice<UInt8>) -> Components? {
        let (rest, build) = splitFirst(Ascii.plus, s)
        let (core, pre) = splitFirst(Ascii.hyphen, rest)
        return assemble(core, pre, build)
    }

    /// 分解したうえで、すべての識別子が文法上妥当な場合だけ成功する。
    ///
    /// Lean: `SemVer.parse`
    static func parse(_ s: ArraySlice<UInt8>) -> Components? {
        guard let c = decompose(s), c.isWellFormed else {
            return nil
        }
        return c
    }

    // MARK: 構成要素から文字列へ

    /// 識別子の列をドットで連結する。列が空なら、その部分自体がない。
    ///
    /// Lean: `SemVer.joinIdentifiers`(内部の連結は `SemVer.join`)
    static func joinIdentifiers(_ identifiers: [[UInt8]]) -> [UInt8]? {
        guard let first = identifiers.first else {
            return nil
        }
        var out = first
        for identifier in identifiers.dropFirst() {
            out.append(Ascii.dot)
            out.append(contentsOf: identifier)
        }
        return out
    }

    /// 省略可能な後続部分を、区切りバイトを前に付けて文字列に戻す。
    ///
    /// Lean: `SemVer.suffix`
    static func suffix(_ sep: UInt8, _ s: [UInt8]?) -> [UInt8] {
        guard let s else {
            return []
        }
        return [sep] + s
    }

    /// 構成要素をバージョン文字列に戻す。
    ///
    /// Lean: `Components.render`
    static func render(_ c: Components) -> [UInt8] {
        c.major + [Ascii.dot] + c.minor + [Ascii.dot] + c.patch
            + suffix(Ascii.hyphen, joinIdentifiers(c.preRelease))
            + suffix(Ascii.plus, joinIdentifiers(c.build))
    }
}
