import SemVer.Parser.Split
import SemVer.Spec.Components
import SemVer.Theorems.Identifiers

/-!
# 構成要素への分解(参照パーサ)

バージョン文字列を、識別子をバイト列のまま持つ構成要素(`Spec.Components`)に分ける。

ここでの `parse` は読みやすさを優先した参照実装で、効率は考えない。
BNF との同値性は `SemVer.Parser.Correctness` で証明する。
-/

namespace SemVer

open Spec

instance (c : Components) : Decidable c.WF :=
  decidable_of_iff
    (NumericIdentifier c.major ∧ NumericIdentifier c.minor ∧ NumericIdentifier c.patch ∧
      (∀ i ∈ c.preRelease, PreReleaseIdentifier i) ∧ (∀ i ∈ c.build, BuildIdentifier i))
    ⟨fun ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩,
     fun ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩⟩

/-! ## 文字列への変換 -/

/-- 識別子の列をドットで連結する。列が空なら、その部分自体がない。 -/
def joinIdentifiers : List (List Byte) → Option (List Byte)
  | [] => none
  | i :: is => some (join Ascii.dot i is)

/-- 構成要素をバージョン文字列に戻す。 -/
def Spec.Components.render (c : Components) : List Byte :=
  (c.major ++ Ascii.dot :: (c.minor ++ Ascii.dot :: c.patch)) ++
    (suffix Ascii.hyphen (joinIdentifiers c.preRelease) ++
      suffix Ascii.plus (joinIdentifiers c.build))

/-! ## 文字列からの分解 -/

/-- `-` または `+` の後ろをドットで識別子に分ける。その部分がなければ空列。 -/
def parseIdentifiers : Option (List Byte) → List (List Byte)
  | none => []
  | some s => (splitOn Ascii.dot s).1 :: (splitOn Ascii.dot s).2

/-- コア部分をドットで 3 つに分け、構成要素を組み立てる。ちょうど 3 つでなければ失敗する。 -/
def assemble (core : List Byte) (pre build : Option (List Byte)) : Option Components :=
  match splitOn Ascii.dot core with
  | (major, [minor, patch]) =>
    some {
      major, minor, patch
      preRelease := parseIdentifiers pre
      build := parseIdentifiers build }
  | _ => none

/--
識別子の中身を検査せずに分解する。
最初の `+` でビルドメタデータを切り離し、残りを最初の `-` でコアとプレリリースに分ける。
-/
def decompose (s : List Byte) : Option Components :=
  assemble
    (splitFirst Ascii.hyphen (splitFirst Ascii.plus s).1).1
    (splitFirst Ascii.hyphen (splitFirst Ascii.plus s).1).2
    (splitFirst Ascii.plus s).2

/-- 参照パーサ。分解したうえで、すべての識別子が文法上妥当な場合だけ成功する。 -/
def parse (s : List Byte) : Option Components :=
  match decompose s with
  | some c => if c.WF then some c else none
  | none => none

end SemVer
