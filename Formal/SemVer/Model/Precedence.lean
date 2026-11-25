import SemVer.Spec.Denotation
import SemVer.Spec.Decidable
import SemVer.Theorems.Identifiers

/-!
# 構成要素の上での優先順位(実装モデル)

`Components` をバイト列のまま比較する方法を定める。数値識別子を整数に変換しないので、
桁数に上限がなく、オーバーフローも起きない。Swift 実装の `<` と `==` はこの定義を写す。

仕様の優先順位(`Version.Lt`)と一致することは `SemVer.Model.Correctness` で証明する。
-/

namespace SemVer

open Spec

/-- 数値識別子の比較。桁数が少ない方が小さく、桁数が同じなら辞書順で比べる。 -/
def NumericLt (a b : List Byte) : Prop :=
  a.length < b.length ∨ (a.length = b.length ∧ LexLt AsciiLt a b)

instance (a b : List Byte) : Decidable (NumericLt a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/--
プレリリース識別子の比較。数字だけの識別子同士は数値として、そうでない識別子同士は ASCII 順で比べ、
数字だけの識別子はそうでない識別子より常に小さい。
-/
def IdentifierLt (a b : List Byte) : Prop :=
  if ∀ c ∈ a, IsDigit c then
    (if ∀ c ∈ b, IsDigit c then NumericLt a b else True)
  else
    (if ∀ c ∈ b, IsDigit c then False else LexLt AsciiLt a b)

instance (a b : List Byte) : Decidable (IdentifierLt a b) :=
  inferInstanceAs (Decidable (
    if ∀ c ∈ a, IsDigit c then
      (if ∀ c ∈ b, IsDigit c then NumericLt a b else True)
    else
      (if ∀ c ∈ b, IsDigit c then False else LexLt AsciiLt a b)))

/-- プレリリース識別子の列の比較。空(通常バージョン)が最も高い。 -/
def PreReleaseBytesLt : List (List Byte) → List (List Byte) → Prop
  | [], _ => False
  | _ :: _, [] => True
  | a :: as, b :: bs => LexLt IdentifierLt (a :: as) (b :: bs)

instance PreReleaseBytesLt.decidable :
    (p q : List (List Byte)) → Decidable (PreReleaseBytesLt p q)
  | [], _ => isFalse (fun h => h)
  | _ :: _, [] => isTrue True.intro
  | a :: as, b :: bs => inferInstanceAs (Decidable (LexLt IdentifierLt (a :: as) (b :: bs)))

/-- 構成要素の優先順位。ビルドメタデータは使わない。 -/
def Spec.Components.Lt (c d : Components) : Prop :=
  NumericLt c.major d.major ∨ (c.major = d.major ∧
    (NumericLt c.minor d.minor ∨ (c.minor = d.minor ∧
      (NumericLt c.patch d.patch ∨ (c.patch = d.patch ∧
        PreReleaseBytesLt c.preRelease d.preRelease)))))

instance (c d : Components) : Decidable (c.Lt d) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- 構成要素の優先順位が等しい。ビルドメタデータ以外がすべて一致する。 -/
def Spec.Components.PrecedenceEq (c d : Components) : Prop :=
  c.major = d.major ∧ c.minor = d.minor ∧ c.patch = d.patch ∧ c.preRelease = d.preRelease

instance (c d : Components) : Decidable (c.PrecedenceEq d) :=
  inferInstanceAs (Decidable (_ ∧ _))

end SemVer
