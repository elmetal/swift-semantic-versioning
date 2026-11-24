/-!
# Semantic Versioning 2.0.0 — BNF 文法

出典: Semantic Versioning 2.0.0 "Backus–Naur Form Grammar for Valid SemVer Versions"
<https://semver.org/spec/v2.0.0.html>(CC BY 3.0)

このファイルは信頼の基点である。各定義は BNF の生成規則 1 本を構成子 1 個に写したもので、
判定の都合による言い換えを含めない。言い換え(判定手続き、正規表現、DFA)は別ファイルで定義し、
ここでの定義との同値性を証明する。
-/

namespace SemVer.Spec

/-- 入力記号。Swift 側の `UInt8`(UTF-8 コードユニット)に対応する。 -/
abbrev Byte := UInt8

namespace Ascii

/-- `"0"` -/
abbrev zero : Byte := 0x30
/-- `"."` -/
abbrev dot : Byte := 0x2E
/-- `"-"` -/
abbrev hyphen : Byte := 0x2D
/-- `"+"` -/
abbrev plus : Byte := 0x2B

end Ascii

/-! ## 文字クラス -/

/-- `<positive digit> ::= "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"` -/
def IsPositiveDigit (c : Byte) : Prop := 0x31 ≤ c ∧ c ≤ 0x39

/-- `<digit> ::= "0" | <positive digit>` -/
def IsDigit (c : Byte) : Prop := c = Ascii.zero ∨ IsPositiveDigit c

/-- `<letter> ::= "A" | … | "Z" | "a" | … | "z"` -/
def IsLetter (c : Byte) : Prop := (0x41 ≤ c ∧ c ≤ 0x5A) ∨ (0x61 ≤ c ∧ c ≤ 0x7A)

/-- `<non-digit> ::= <letter> | "-"` -/
def IsNonDigit (c : Byte) : Prop := IsLetter c ∨ c = Ascii.hyphen

/-- `<identifier character> ::= <digit> | <non-digit>` -/
def IsIdentifierCharacter (c : Byte) : Prop := IsDigit c ∨ IsNonDigit c

instance (c : Byte) : Decidable (IsPositiveDigit c) :=
  inferInstanceAs (Decidable (0x31 ≤ c ∧ c ≤ 0x39))

instance (c : Byte) : Decidable (IsDigit c) :=
  inferInstanceAs (Decidable (c = Ascii.zero ∨ IsPositiveDigit c))

instance (c : Byte) : Decidable (IsLetter c) :=
  inferInstanceAs (Decidable ((0x41 ≤ c ∧ c ≤ 0x5A) ∨ (0x61 ≤ c ∧ c ≤ 0x7A)))

instance (c : Byte) : Decidable (IsNonDigit c) :=
  inferInstanceAs (Decidable (IsLetter c ∨ c = Ascii.hyphen))

instance (c : Byte) : Decidable (IsIdentifierCharacter c) :=
  inferInstanceAs (Decidable (IsDigit c ∨ IsNonDigit c))

/-! ## 識別子 -/

/-- `<digits> ::= <digit> | <digit> <digits>` -/
inductive Digits : List Byte → Prop where
  | single {d : Byte} : IsDigit d → Digits [d]
  | cons {d : Byte} {ds : List Byte} : IsDigit d → Digits ds → Digits (d :: ds)

/-- `<identifier characters> ::= <identifier character>
                             | <identifier character> <identifier characters>` -/
inductive IdentifierCharacters : List Byte → Prop where
  | single {c : Byte} : IsIdentifierCharacter c → IdentifierCharacters [c]
  | cons {c : Byte} {cs : List Byte} :
      IsIdentifierCharacter c → IdentifierCharacters cs → IdentifierCharacters (c :: cs)

/-- `<numeric identifier> ::= "0" | <positive digit> | <positive digit> <digits>` -/
inductive NumericIdentifier : List Byte → Prop where
  | zero : NumericIdentifier [Ascii.zero]
  | positive {d : Byte} : IsPositiveDigit d → NumericIdentifier [d]
  | positiveDigits {d : Byte} {ds : List Byte} :
      IsPositiveDigit d → Digits ds → NumericIdentifier (d :: ds)

/-- `<alphanumeric identifier> ::= <non-digit>
                               | <non-digit> <identifier characters>
                               | <identifier characters> <non-digit>
                               | <identifier characters> <non-digit> <identifier characters>` -/
inductive AlphanumericIdentifier : List Byte → Prop where
  | nonDigit {c : Byte} : IsNonDigit c → AlphanumericIdentifier [c]
  | nonDigitChars {c : Byte} {cs : List Byte} :
      IsNonDigit c → IdentifierCharacters cs → AlphanumericIdentifier (c :: cs)
  | charsNonDigit {cs : List Byte} {c : Byte} :
      IdentifierCharacters cs → IsNonDigit c → AlphanumericIdentifier (cs ++ [c])
  | charsNonDigitChars {cs : List Byte} {c : Byte} {cs' : List Byte} :
      IdentifierCharacters cs → IsNonDigit c → IdentifierCharacters cs' →
      AlphanumericIdentifier (cs ++ c :: cs')

/-- `<pre-release identifier> ::= <alphanumeric identifier> | <numeric identifier>` -/
inductive PreReleaseIdentifier : List Byte → Prop where
  | alphanumeric {s : List Byte} : AlphanumericIdentifier s → PreReleaseIdentifier s
  | numeric {s : List Byte} : NumericIdentifier s → PreReleaseIdentifier s

/-- `<build identifier> ::= <alphanumeric identifier> | <digits>` -/
inductive BuildIdentifier : List Byte → Prop where
  | alphanumeric {s : List Byte} : AlphanumericIdentifier s → BuildIdentifier s
  | digits {s : List Byte} : Digits s → BuildIdentifier s

/-! ## プレリリースとビルドメタデータ -/

/-- `<dot-separated pre-release identifiers> ::= <pre-release identifier>
      | <pre-release identifier> "." <dot-separated pre-release identifiers>` -/
inductive DotSeparatedPreReleaseIdentifiers : List Byte → Prop where
  | single {i : List Byte} : PreReleaseIdentifier i → DotSeparatedPreReleaseIdentifiers i
  | cons {i rest : List Byte} :
      PreReleaseIdentifier i → DotSeparatedPreReleaseIdentifiers rest →
      DotSeparatedPreReleaseIdentifiers (i ++ Ascii.dot :: rest)

/-- `<dot-separated build identifiers> ::= <build identifier>
      | <build identifier> "." <dot-separated build identifiers>` -/
inductive DotSeparatedBuildIdentifiers : List Byte → Prop where
  | single {i : List Byte} : BuildIdentifier i → DotSeparatedBuildIdentifiers i
  | cons {i rest : List Byte} :
      BuildIdentifier i → DotSeparatedBuildIdentifiers rest →
      DotSeparatedBuildIdentifiers (i ++ Ascii.dot :: rest)

/-- `<pre-release> ::= <dot-separated pre-release identifiers>` -/
abbrev PreRelease (s : List Byte) : Prop := DotSeparatedPreReleaseIdentifiers s

/-- `<build> ::= <dot-separated build identifiers>` -/
abbrev Build (s : List Byte) : Prop := DotSeparatedBuildIdentifiers s

/-! ## バージョン全体 -/

/-- `<major> ::= <numeric identifier>` -/
abbrev Major (s : List Byte) : Prop := NumericIdentifier s

/-- `<minor> ::= <numeric identifier>` -/
abbrev Minor (s : List Byte) : Prop := NumericIdentifier s

/-- `<patch> ::= <numeric identifier>` -/
abbrev Patch (s : List Byte) : Prop := NumericIdentifier s

/-- `<version core> ::= <major> "." <minor> "." <patch>` -/
inductive VersionCore : List Byte → Prop where
  | mk {major minor patch : List Byte} :
      Major major → Minor minor → Patch patch →
      VersionCore (major ++ Ascii.dot :: (minor ++ Ascii.dot :: patch))

/-- `<valid semver> ::= <version core>
                    | <version core> "-" <pre-release>
                    | <version core> "+" <build>
                    | <version core> "-" <pre-release> "+" <build>` -/
inductive ValidSemVer : List Byte → Prop where
  | core {c : List Byte} : VersionCore c → ValidSemVer c
  | corePreRelease {c p : List Byte} :
      VersionCore c → PreRelease p → ValidSemVer (c ++ Ascii.hyphen :: p)
  | coreBuild {c b : List Byte} :
      VersionCore c → Build b → ValidSemVer (c ++ Ascii.plus :: b)
  | corePreReleaseBuild {c p b : List Byte} :
      VersionCore c → PreRelease p → Build b →
      ValidSemVer (c ++ Ascii.hyphen :: (p ++ Ascii.plus :: b))

end SemVer.Spec
