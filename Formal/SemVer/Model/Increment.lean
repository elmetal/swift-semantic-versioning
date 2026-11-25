import SemVer.Spec.Components

/-!
# 構成要素の上での繰り上げ(実装モデル)

数値識別子を整数に変換せず、数字列のまま 1 を足す。桁数に上限がないので、オーバーフローは起きない。
Swift 実装の `nextPatch` などはこの定義を写す。

仕様の繰り上げ(`Version.nextPatch` など)と一致することは `SemVer.Model.IncrementCorrectness` で証明する。
-/

namespace SemVer

open Spec

/--
数字列に 1 を足す。同じ桁数の結果と、最上位からの繰り上がりがあったかどうかを返す。
繰り上がりがあるのは、すべての桁が `9` のときだけである。
-/
def succAux : List Byte → List Byte × Bool
  | [] => ([], true)
  | c :: cs =>
    if (succAux cs).2 then
      (if c = 0x39 then (Ascii.zero :: (succAux cs).1, true)
       else ((c + 1) :: (succAux cs).1, false))
    else (c :: (succAux cs).1, false)

/-- 数値識別子に 1 を足す。最上位から繰り上がったら、先頭に `1` を補う。 -/
def succDigits (s : List Byte) : List Byte :=
  if (succAux s).2 then 0x31 :: (succAux s).1 else (succAux s).1

/-- パッチの繰り上げ。プレリリース版なら、対応する通常バージョンにする。 -/
def Spec.Components.nextPatch (c : Components) : Components :=
  if c.preRelease = [] then
    { major := c.major, minor := c.minor, patch := succDigits c.patch,
      preRelease := [], build := [] }
  else
    { major := c.major, minor := c.minor, patch := c.patch, preRelease := [], build := [] }

/-- マイナーの繰り上げ。パッチが 0 のプレリリース版なら、対応する通常バージョンにする。 -/
def Spec.Components.nextMinor (c : Components) : Components :=
  if c.patch ≠ [Ascii.zero] ∨ c.preRelease = [] then
    { major := c.major, minor := succDigits c.minor, patch := [Ascii.zero],
      preRelease := [], build := [] }
  else
    { major := c.major, minor := c.minor, patch := [Ascii.zero], preRelease := [], build := [] }

/-- メジャーの繰り上げ。マイナーとパッチが 0 のプレリリース版なら、対応する通常バージョンにする。 -/
def Spec.Components.nextMajor (c : Components) : Components :=
  if c.minor ≠ [Ascii.zero] ∨ c.patch ≠ [Ascii.zero] ∨ c.preRelease = [] then
    { major := succDigits c.major, minor := [Ascii.zero], patch := [Ascii.zero],
      preRelease := [], build := [] }
  else
    { major := c.major, minor := [Ascii.zero], patch := [Ascii.zero],
      preRelease := [], build := [] }

end SemVer
