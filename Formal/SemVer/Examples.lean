import SemVer.Spec.Decidable
import SemVer.Spec.Increment

/-!
# 仕様の例による点検

形式仕様そのものの書き間違いを見つけるための検査。仕様書に載っている具体例を評価し、
期待と違えばビルドが失敗する。これは証明ではなくテストである。
-/

namespace SemVer.Spec.Examples

/-! ## 文字クラス -/

private def bytesWhere (p : Byte → Bool) : List Nat :=
  (List.range 256).filter fun n => p n.toUInt8

private def codes (s : String) : List Nat := s.toList.map Char.toNat

#guard bytesWhere (fun c => decide (IsPositiveDigit c)) = codes "123456789"
#guard bytesWhere (fun c => decide (IsDigit c)) = codes "0123456789"
#guard bytesWhere (fun c => decide (IsLetter c))
  = codes "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
#guard bytesWhere (fun c => decide (IsNonDigit c))
  = codes "-ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
#guard bytesWhere (fun c => decide (IsIdentifierCharacter c))
  = codes "-0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
#guard [Ascii.zero, Ascii.dot, Ascii.hyphen, Ascii.plus].map (·.toNat) = codes "0.-+"

/-! ## 文法 -/

/-- `10` は数値識別子。 -/
example : NumericIdentifier [0x31, 0x30] :=
  .positiveDigits (by decide) (.single (by decide))

/-- `01` は先頭ゼロがあるので数値識別子ではない(§2, §9)。 -/
example : ¬ NumericIdentifier [0x30, 0x31] := by
  intro h
  cases h with
  | positiveDigits hd _ => exact absurd hd (by decide)

/-- `0a` は英数字識別子(先頭ゼロの制約は数値識別子だけに掛かる)。 -/
example : AlphanumericIdentifier [0x30, 0x61] :=
  .charsNonDigit (cs := [0x30]) (.single (by decide)) (by decide)

/-- `1.0.0` -/
example : ValidSemVer [0x31, 0x2E, 0x30, 0x2E, 0x30] :=
  .core (.mk (major := [0x31]) (minor := [0x30]) (patch := [0x30])
    (.positive (by decide)) .zero .zero)

/-- `1.0.0-a+01`(ビルド識別子は先頭ゼロを許す) -/
example : ValidSemVer [0x31, 0x2E, 0x30, 0x2E, 0x30, 0x2D, 0x61, 0x2B, 0x30, 0x31] :=
  .corePreReleaseBuild (c := [0x31, 0x2E, 0x30, 0x2E, 0x30]) (p := [0x61]) (b := [0x30, 0x31])
    (.mk (major := [0x31]) (minor := [0x30]) (patch := [0x30])
      (.positive (by decide)) .zero .zero)
    (.single (.alphanumeric (.nonDigit (by decide))))
    (.single (.digits (.cons (by decide) (.single (by decide)))))

/-! ## 優先順位(§11) -/

private def a (s : String) : PreReleaseId := .alphanumeric s.toUTF8.toList
private def n (k : Nat) : PreReleaseId := .numeric k
private def v (major minor patch : Nat) (pre : List PreReleaseId := []) : Version :=
  { major, minor, patch, preRelease := pre }

/-- 列が優先順位について狭義単調増加である。 -/
private def increasing : List Version → Bool
  | [] => true
  | x :: xs => xs.all (fun y => decide (x.Lt y) && !decide (y.Lt x)) && increasing xs

/- §11.2 の例: 1.0.0 < 2.0.0 < 2.1.0 < 2.1.1 -/
#guard increasing [v 1 0 0, v 2 0 0, v 2 1 0, v 2 1 1]

/- §11.3 の例: 1.0.0-alpha < 1.0.0 -/
#guard increasing [v 1 0 0 [a "alpha"], v 1 0 0]

/- §11.4 の例: 1.0.0-alpha < 1.0.0-alpha.1 < 1.0.0-alpha.beta < 1.0.0-beta
   < 1.0.0-beta.2 < 1.0.0-beta.11 < 1.0.0-rc.1 < 1.0.0 -/
#guard increasing [
  v 1 0 0 [a "alpha"],
  v 1 0 0 [a "alpha", n 1],
  v 1 0 0 [a "alpha", a "beta"],
  v 1 0 0 [a "beta"],
  v 1 0 0 [a "beta", n 2],
  v 1 0 0 [a "beta", n 11],
  v 1 0 0 [a "rc", n 1],
  v 1 0 0]

/- §10 の例: ビルドメタデータだけが違うバージョンは優先順位が等しい。 -/
#guard
  let x : Version := { v 1 0 0 [a "alpha"] with build := ["001".toUTF8.toList] }
  let y : Version := { v 1 0 0 [a "alpha"] with build := ["exp".toUTF8.toList, "sha".toUTF8.toList] }
  decide (x.PrecedenceEq y) && !decide (x.Lt y) && !decide (y.Lt x) && x != y

/- §11.4.2: ASCII 順では大文字が小文字より前、ハイフンが英数字より前。 -/
#guard increasing [v 1 0 0 [a "-"], v 1 0 0 [a "A"], v 1 0 0 [a "a"]]

/-! ## 繰り上げ(§6〜§8) -/

#guard (v 1 2 3).nextPatch = v 1 2 4
#guard (v 1 2 3).nextMinor = v 1 3 0
#guard (v 1 2 3).nextMajor = v 2 0 0

end SemVer.Spec.Examples
