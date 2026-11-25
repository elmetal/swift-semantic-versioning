import SemVer.Spec.Components
import SemVer.Spec.Precedence

/-!
# 構成要素の意味

出典: <https://semver.org/spec/v2.0.0.html>(CC BY 3.0)

このファイルは信頼の基点である。バイト列で持っている構成要素が、どの抽象的なバージョンを表すかを定める。

* §2: X, Y, Z は非負整数。数字列は 10 進表記として読む。
* §11.4.1: 数字だけからなるプレリリース識別子は数値として扱う。それ以外はバイト列のまま扱う。
-/

namespace SemVer.Spec

/-- 数字 1 文字の値。 -/
def digitValue (c : Byte) : Nat := c.toNat - Ascii.zero.toNat

/-- 10 進表記を左から 1 桁読み進める。 -/
def decimalStep (acc : Nat) (c : Byte) : Nat := acc * 10 + digitValue c

/-- 数字列を 10 進表記として読んだ値。 -/
def decimalValue (s : List Byte) : Nat := s.foldl decimalStep 0

/-- プレリリース識別子のバイト列が表す値。 -/
def PreReleaseId.ofBytes (i : List Byte) : PreReleaseId :=
  if ∀ c ∈ i, IsDigit c then .numeric (decimalValue i) else .alphanumeric i

/-- 構成要素が表すバージョン。 -/
def Components.toVersion (c : Components) : Version where
  major := decimalValue c.major
  minor := decimalValue c.minor
  patch := decimalValue c.patch
  preRelease := c.preRelease.map PreReleaseId.ofBytes
  build := c.build

/-- プレリリース識別子の値が文法上妥当である。 -/
def PreReleaseId.WF : PreReleaseId → Prop
  | .numeric _ => True
  | .alphanumeric s => AlphanumericIdentifier s

/-- バージョンの値が文法上妥当である(何らかの妥当な文字列が表す値である)。 -/
structure Version.WF (v : Version) : Prop where
  preRelease : ∀ i ∈ v.preRelease, i.WF
  build : ∀ i ∈ v.build, BuildIdentifier i

end SemVer.Spec
