// Semantic Versioning 2.0.0 の文法(文字クラスと識別子)。
//
// 各関数は Formal/ の Lean 定義を写したもので、対応する定義または定理をコメントに記す。
// 識別子の判定は BNF そのものではなく、BNF と同値だと証明済みの条件
// (Formal/SemVer/Theorems/Identifiers.lean)を使う。

/// 区切り記号と数字の ASCII コード。Lean: `SemVer.Spec.Ascii`(`1` と `9` は Lean では `0x31`、`0x39` と直接書く)
enum Ascii {
    static let zero: UInt8 = 0x30
    static let one: UInt8 = 0x31
    static let nine: UInt8 = 0x39
    static let dot: UInt8 = 0x2E
    static let hyphen: UInt8 = 0x2D
    static let plus: UInt8 = 0x2B
}

enum Grammar {
    /// Lean: `IsPositiveDigit`
    static func isPositiveDigit(_ c: UInt8) -> Bool {
        0x31 <= c && c <= 0x39
    }

    /// Lean: `IsDigit`
    static func isDigit(_ c: UInt8) -> Bool {
        c == Ascii.zero || isPositiveDigit(c)
    }

    /// Lean: `IsLetter`
    static func isLetter(_ c: UInt8) -> Bool {
        (0x41 <= c && c <= 0x5A) || (0x61 <= c && c <= 0x7A)
    }

    /// Lean: `IsNonDigit`
    static func isNonDigit(_ c: UInt8) -> Bool {
        isLetter(c) || c == Ascii.hyphen
    }

    /// Lean: `IsIdentifierCharacter`
    static func isIdentifierCharacter(_ c: UInt8) -> Bool {
        isDigit(c) || isNonDigit(c)
    }

    /// 数字だけからなる。Lean: `∀ c ∈ s, IsDigit c`
    static func isAllDigits(_ s: [UInt8]) -> Bool {
        s.allSatisfy(isDigit)
    }

    /// Lean: `Digits`(定理 `digits_iff` の右辺)
    static func isDigits(_ s: [UInt8]) -> Bool {
        !s.isEmpty && isAllDigits(s)
    }

    /// Lean: `NumericIdentifier`(定理 `numericIdentifier_iff` の右辺)
    static func isNumericIdentifier(_ s: [UInt8]) -> Bool {
        s == [Ascii.zero] || (isAllDigits(s) && !s.isEmpty && s.first != Ascii.zero)
    }

    /// Lean: `AlphanumericIdentifier`(定理 `alphanumericIdentifier_iff` の右辺)
    static func isAlphanumericIdentifier(_ s: [UInt8]) -> Bool {
        s.allSatisfy(isIdentifierCharacter) && s.contains(where: isNonDigit)
    }

    /// Lean: `PreReleaseIdentifier`(定理 `preReleaseIdentifier_iff` の右辺)
    static func isPreReleaseIdentifier(_ s: [UInt8]) -> Bool {
        isAlphanumericIdentifier(s) || isNumericIdentifier(s)
    }

    /// Lean: `BuildIdentifier`(定理 `buildIdentifier_iff` の右辺)
    static func isBuildIdentifier(_ s: [UInt8]) -> Bool {
        isAlphanumericIdentifier(s) || isDigits(s)
    }
}

/// バージョン文字列の構成要素。各識別子は UTF-8 のバイト列のまま持つ。
///
/// 数値識別子も数字列のまま持つので、桁数に上限がなく、オーバーフローが起きない。
///
/// Lean: `SemVer.Spec.Components`
struct Components: Equatable, Sendable {
    var major: [UInt8]
    var minor: [UInt8]
    var patch: [UInt8]
    /// プレリリース識別子の列。空なら `-` 以降がない。
    var preRelease: [[UInt8]]
    /// ビルド識別子の列。空なら `+` 以降がない。
    var build: [[UInt8]]

    /// Lean: `Components.WF`
    var isWellFormed: Bool {
        Grammar.isNumericIdentifier(major)
            && Grammar.isNumericIdentifier(minor)
            && Grammar.isNumericIdentifier(patch)
            && preRelease.allSatisfy(Grammar.isPreReleaseIdentifier)
            && build.allSatisfy(Grammar.isBuildIdentifier)
    }
}
