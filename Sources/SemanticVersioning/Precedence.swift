// 構成要素の優先順位(Semantic Versioning 2.0.0 §11)。
//
// Formal/SemVer/Model/Precedence.lean の実装モデルを写したもの。
// 数値識別子を整数に変換せず、バイト列のまま比べる。この比較が §11 の優先順位と一致すること
// (`Components.lt_iff`, `Components.precedenceEq_iff`)が証明されている。

enum Precedence {
    /// 左から比べて最初の相違で決まる辞書式順序。
    /// 先行する要素がすべて等しければ、短い列の方が小さい。
    ///
    /// Lean: `SemVer.Spec.LexLt`
    static func lexLess<T: Equatable>(_ a: [T], _ b: [T], by less: (T, T) -> Bool) -> Bool {
        var i = 0
        while i < a.count && i < b.count {
            if less(a[i], b[i]) {
                return true
            }
            if a[i] != b[i] {
                return false
            }
            i += 1
        }
        return i == a.count && i < b.count
    }

    /// ASCII 順。Lean: `SemVer.Spec.AsciiLt`
    static func asciiLess(_ a: UInt8, _ b: UInt8) -> Bool {
        a < b
    }

    /// 数値識別子の比較。桁数が少ない方が小さく、桁数が同じなら辞書順で比べる。
    ///
    /// Lean: `SemVer.NumericLt`(数値の大小と一致することは `numericLt_iff`)
    static func numericLess(_ a: [UInt8], _ b: [UInt8]) -> Bool {
        a.count < b.count || (a.count == b.count && lexLess(a, b, by: asciiLess))
    }

    /// プレリリース識別子の比較。
    ///
    /// Lean: `SemVer.IdentifierLt`
    static func identifierLess(_ a: [UInt8], _ b: [UInt8]) -> Bool {
        if Grammar.isAllDigits(a) {
            if Grammar.isAllDigits(b) {
                return numericLess(a, b)
            } else {
                return true
            }
        } else {
            if Grammar.isAllDigits(b) {
                return false
            } else {
                return lexLess(a, b, by: asciiLess)
            }
        }
    }

    /// プレリリース識別子の列の比較。空(通常バージョン)が最も高い。
    ///
    /// Lean: `SemVer.PreReleaseBytesLt`
    static func preReleaseLess(_ p: [[UInt8]], _ q: [[UInt8]]) -> Bool {
        if p.isEmpty {
            return false
        }
        if q.isEmpty {
            return true
        }
        return lexLess(p, q, by: identifierLess)
    }

    /// 構成要素の優先順位。ビルドメタデータは使わない。
    ///
    /// Lean: `Components.Lt`
    static func less(_ c: Components, _ d: Components) -> Bool {
        numericLess(c.major, d.major) || (c.major == d.major
            && (numericLess(c.minor, d.minor) || (c.minor == d.minor
                && (numericLess(c.patch, d.patch) || (c.patch == d.patch
                    && preReleaseLess(c.preRelease, d.preRelease))))))
    }

    /// 構成要素の優先順位が等しい。ビルドメタデータ以外がすべて一致する。
    ///
    /// Lean: `Components.PrecedenceEq`
    static func precedenceEqual(_ c: Components, _ d: Components) -> Bool {
        c.major == d.major && c.minor == d.minor && c.patch == d.patch
            && c.preRelease == d.preRelease
    }
}
