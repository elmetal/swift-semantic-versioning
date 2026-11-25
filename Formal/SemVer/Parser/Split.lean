import SemVer.Spec.Grammar

/-!
# 区切りバイトによる分割と結合

参照パーサの部品。`splitOn` と `join`、`splitFirst` と `suffix` がそれぞれ互いに逆であることを示す。
-/

namespace SemVer

open Spec

/-! ## すべての区切りで分割する -/

/-- 区切りバイトで分割する。先頭の区間と、残りの区間の列を返す(区間は必ず 1 個以上ある)。 -/
def splitOn (sep : Byte) : List Byte → List Byte × List (List Byte)
  | [] => ([], [])
  | c :: cs =>
    if c = sep then ([], (splitOn sep cs).1 :: (splitOn sep cs).2)
    else (c :: (splitOn sep cs).1, (splitOn sep cs).2)

/-- 先頭の区間と残りの区間を、区切りバイトを挟んで連結する。 -/
def join (sep : Byte) : List Byte → List (List Byte) → List Byte
  | x, [] => x
  | x, y :: ys => x ++ sep :: join sep y ys

theorem splitOn_cons_sep (sep : Byte) (cs : List Byte) :
    splitOn sep (sep :: cs) = ([], (splitOn sep cs).1 :: (splitOn sep cs).2) := by
  simp [splitOn]

theorem splitOn_cons_ne {sep c : Byte} (h : c ≠ sep) (cs : List Byte) :
    splitOn sep (c :: cs) = (c :: (splitOn sep cs).1, (splitOn sep cs).2) := by
  simp [splitOn, h]

theorem join_cons (sep c : Byte) (x : List Byte) (ys : List (List Byte)) :
    join sep (c :: x) ys = c :: join sep x ys := by
  cases ys <;> rfl

/-- 分割してから結合すると元に戻る。 -/
theorem join_splitOn (sep : Byte) (s : List Byte) :
    join sep (splitOn sep s).1 (splitOn sep s).2 = s := by
  induction s with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : c = sep
    · subst h
      simp [splitOn_cons_sep, join, ih]
    · simp [splitOn_cons_ne h, join_cons, ih]

theorem splitOn_append_of_not_mem {sep : Byte} {x : List Byte} (hx : sep ∉ x) (t : List Byte) :
    splitOn sep (x ++ t) = (x ++ (splitOn sep t).1, (splitOn sep t).2) := by
  induction x with
  | nil => simp
  | cons c x ih =>
    have hc : c ≠ sep := fun h => hx (by simp [h])
    have hx' : sep ∉ x := fun h => hx (List.mem_cons_of_mem _ h)
    simp [splitOn_cons_ne hc, ih hx']

/-- 区切りバイトを含まない区間を結合してから分割すると、元の区間に戻る。 -/
theorem splitOn_join {sep : Byte} : ∀ (ys : List (List Byte)) (x : List Byte),
    sep ∉ x → (∀ y ∈ ys, sep ∉ y) → splitOn sep (join sep x ys) = (x, ys)
  | [], x, hx, _ => by
    have h := splitOn_append_of_not_mem hx []
    simpa [join, splitOn] using h
  | y :: ys, x, hx, hys => by
    have ih := splitOn_join ys y (hys y (by simp))
      (fun z hz => hys z (List.mem_cons_of_mem _ hz))
    rw [join, splitOn_append_of_not_mem hx, splitOn_cons_sep, ih]
    simp

/-- 結合した結果のバイトは、区切りバイトか、いずれかの区間のバイトである。 -/
theorem forall_mem_join {q : Byte → Prop} {sep : Byte} (hsep : q sep) :
    ∀ (ys : List (List Byte)) (x : List Byte),
      (∀ b ∈ x, q b) → (∀ y ∈ ys, ∀ b ∈ y, q b) → ∀ b ∈ join sep x ys, q b
  | [], _, hx, _ => hx
  | y :: ys, x, hx, hys => by
    intro b hb
    rw [join] at hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hx b hb
    · rcases List.mem_cons.mp hb with heq | hb
      · exact heq ▸ hsep
      · exact forall_mem_join hsep ys y (hys y (by simp))
          (fun z hz => hys z (List.mem_cons_of_mem _ hz)) b hb

/-! ## 最初の区切りで分割する -/

/-- 最初の区切りバイトの前と後ろに分ける。区切りバイトがなければ後ろは `none`。 -/
def splitFirst (sep : Byte) : List Byte → List Byte × Option (List Byte)
  | [] => ([], none)
  | c :: cs =>
    if c = sep then ([], some cs)
    else (c :: (splitFirst sep cs).1, (splitFirst sep cs).2)

/-- 省略可能な後続部分を、区切りバイトを前に付けて文字列に戻す。 -/
def suffix (sep : Byte) : Option (List Byte) → List Byte
  | none => []
  | some t => sep :: t

/-- 最初の区切りで分けてから戻すと元に戻る。 -/
theorem splitFirst_reassemble (sep : Byte) (s : List Byte) :
    (splitFirst sep s).1 ++ suffix sep (splitFirst sep s).2 = s := by
  induction s with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : c = sep
    · simp [splitFirst, h, suffix]
    · simp [splitFirst, h, ih]

/-- 区切りバイトを含まない前半に後続部分を付けてから分けると、元の組に戻る。 -/
theorem splitFirst_append_suffix {sep : Byte} {a : List Byte} (ha : sep ∉ a)
    (o : Option (List Byte)) : splitFirst sep (a ++ suffix sep o) = (a, o) := by
  induction a with
  | nil => cases o <;> simp [splitFirst, suffix]
  | cons c a ih =>
    have hc : c ≠ sep := fun h => ha (by simp [h])
    have ha' : sep ∉ a := fun h => ha (List.mem_cons_of_mem _ h)
    simp [splitFirst, hc, ih ha']

end SemVer
