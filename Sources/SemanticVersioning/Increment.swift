// 数字列の演算と、構成要素の繰り上げ。
//
// Formal/SemVer/Model/Increment.lean の実装モデルを写したもの。
// 数値識別子を整数に変換せず、数字列のまま 1 を足すので、桁数に上限がなくオーバーフローが起きない。
// この繰り上げが仕様の繰り上げと一致すること(`Components.toVersion_nextPatch` ほか)と、
// 結果が「その種類のリリースのうち、元より高くて最も低いもの」であること
// (`Version.nextPatch_isLeast` ほか)が証明されている。

enum Digits {
    /// 自然数の 10 進表記(先頭ゼロなし)。
    ///
    /// Lean: `SemVer.Spec.decimalDigits`(数値識別子になることは `numericIdentifier_decimalDigits`)
    static func decimal(_ n: UInt) -> [UInt8] {
        if n < 10 {
            return [Ascii.zero + UInt8(n)]
        } else {
            return decimal(n / 10) + [Ascii.zero + UInt8(n % 10)]
        }
    }

    /// 数値識別子に 1 を足す。
    ///
    /// 下の桁から見て、`9` は `0` にして上の桁へ進み、`9` 以外は 1 増やして終わる。
    /// すべての桁が `9` だったら、先頭に `1` を補う。
    ///
    /// Lean: `SemVer.succDigits`(値がちょうど 1 増えることは `succDigits_spec`)
    static func successor(_ s: [UInt8]) -> [UInt8] {
        var out = s
        var i = out.count
        while i > 0 {
            i -= 1
            if out[i] == Ascii.nine {
                out[i] = Ascii.zero
            } else {
                out[i] += 1
                return out
            }
        }
        return [Ascii.one] + out
    }
}

enum Increment {
    /// パッチの繰り上げ。プレリリース版なら、対応する通常バージョンにする。
    ///
    /// Lean: `Components.nextPatch`
    static func nextPatch(_ c: Components) -> Components {
        if c.preRelease.isEmpty {
            return Components(
                major: c.major, minor: c.minor, patch: Digits.successor(c.patch),
                preRelease: [], build: [])
        } else {
            return Components(
                major: c.major, minor: c.minor, patch: c.patch,
                preRelease: [], build: [])
        }
    }

    /// マイナーの繰り上げ。パッチが 0 のプレリリース版なら、対応する通常バージョンにする。
    ///
    /// Lean: `Components.nextMinor`
    static func nextMinor(_ c: Components) -> Components {
        if c.patch != [Ascii.zero] || c.preRelease.isEmpty {
            return Components(
                major: c.major, minor: Digits.successor(c.minor), patch: [Ascii.zero],
                preRelease: [], build: [])
        } else {
            return Components(
                major: c.major, minor: c.minor, patch: [Ascii.zero],
                preRelease: [], build: [])
        }
    }

    /// メジャーの繰り上げ。マイナーとパッチが 0 のプレリリース版なら、対応する通常バージョンにする。
    ///
    /// Lean: `Components.nextMajor`
    static func nextMajor(_ c: Components) -> Components {
        if c.minor != [Ascii.zero] || c.patch != [Ascii.zero] || c.preRelease.isEmpty {
            return Components(
                major: Digits.successor(c.major), minor: [Ascii.zero], patch: [Ascii.zero],
                preRelease: [], build: [])
        } else {
            return Components(
                major: c.major, minor: [Ascii.zero], patch: [Ascii.zero],
                preRelease: [], build: [])
        }
    }
}
