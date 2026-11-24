import SemVer.Spec.Denotation
import SemVer.Theorems.Identifiers

/-!
# 構成要素と抽象的なバージョンの対応

`Components.toVersion` の逆 `Version.toComponents` を定義し、妥当なもの同士で互いに逆であることを示す。
要点は、先頭ゼロのない数字列と自然数が 10 進表記で 1 対 1 に対応すること。
-/

namespace SemVer.Spec

/-! ## 数字 1 文字 -/

/-- 0〜9 の値を表す数字のバイト。 -/
def digitByte : Nat → Byte
  | 0 => 0x30
  | 1 => 0x31
  | 2 => 0x32
  | 3 => 0x33
  | 4 => 0x34
  | 5 => 0x35
  | 6 => 0x36
  | 7 => 0x37
  | 8 => 0x38
  | _ => 0x39

theorem digitByte_zero : digitByte 0 = Ascii.zero := rfl

theorem toNat_digitByte : ∀ n, n < 10 → (digitByte n).toNat = 48 + n := by decide

theorem digitValue_digitByte : ∀ n, n < 10 → digitValue (digitByte n) = n := by decide

theorem isDigit_digitByte : ∀ n, n < 10 → IsDigit (digitByte n) := by decide

theorem isPositiveDigit_digitByte : ∀ n, n < 10 → 0 < n → IsPositiveDigit (digitByte n) := by
  decide

theorem IsDigit.toNat_bounds {c : Byte} (h : IsDigit c) : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  rcases h with rfl | ⟨h₁, h₂⟩
  · decide
  · have h₁' := UInt8.le_iff_toNat_le.mp h₁
    have h₂' := UInt8.le_iff_toNat_le.mp h₂
    have e₁ : (0x31 : UInt8).toNat = 49 := rfl
    have e₂ : (0x39 : UInt8).toNat = 57 := rfl
    omega

theorem IsDigit.digitValue_lt {c : Byte} (h : IsDigit c) : digitValue c < 10 := by
  have hb := h.toNat_bounds
  have e : Ascii.zero.toNat = 48 := rfl
  unfold digitValue
  omega

theorem IsPositiveDigit.digitValue_pos {c : Byte} (h : IsPositiveDigit c) : 0 < digitValue c := by
  obtain ⟨h₁, _⟩ := h
  have h₁' := UInt8.le_iff_toNat_le.mp h₁
  have e₁ : (0x31 : UInt8).toNat = 49 := rfl
  have e : Ascii.zero.toNat = 48 := rfl
  unfold digitValue
  omega

theorem IsDigit.digitByte_digitValue {c : Byte} (h : IsDigit c) : digitByte (digitValue c) = c := by
  apply UInt8.toNat_inj.mp
  rw [toNat_digitByte _ h.digitValue_lt]
  have hb := h.toNat_bounds
  have e : Ascii.zero.toNat = 48 := rfl
  unfold digitValue
  omega

/-- 非数字(英字とハイフン)は数字ではない。 -/
theorem IsNonDigit.not_isDigit {c : Byte} (h : IsNonDigit c) : ¬ IsDigit c := by
  intro hd
  have hb := hd.toNat_bounds
  rcases h with (⟨h₁, _⟩ | ⟨h₁, _⟩) | rfl
  · have h₁' := UInt8.le_iff_toNat_le.mp h₁
    have e : (0x41 : UInt8).toNat = 65 := rfl
    omega
  · have h₁' := UInt8.le_iff_toNat_le.mp h₁
    have e : (0x61 : UInt8).toNat = 97 := rfl
    omega
  · exact not_isDigit_hyphen hd

/-! ## 自然数の 10 進表記 -/

/-- 自然数の 10 進表記(先頭ゼロなし)。 -/
def decimalDigits (n : Nat) : List Byte :=
  if n < 10 then [digitByte n] else decimalDigits (n / 10) ++ [digitByte (n % 10)]
termination_by n
decreasing_by omega

theorem decimalDigits_of_lt {n : Nat} (h : n < 10) : decimalDigits n = [digitByte n] := by
  rw [decimalDigits, ite_eq_left h]

theorem decimalDigits_of_ge {n : Nat} (h : ¬ n < 10) :
    decimalDigits n = decimalDigits (n / 10) ++ [digitByte (n % 10)] := by
  rw [decimalDigits, ite_eq_right h]

theorem decimalValue_append_singleton (s : List Byte) (c : Byte) :
    decimalValue (s ++ [c]) = decimalValue s * 10 + digitValue c := by
  simp [decimalValue, List.foldl_append, decimalStep]

/-- 10 進表記にしてから読むと元の数に戻る。 -/
theorem decimalValue_decimalDigits (n : Nat) : decimalValue (decimalDigits n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 10
    · rw [decimalDigits_of_lt h]
      simp [decimalValue, decimalStep, digitValue_digitByte n h]
    · have hmod : n % 10 < 10 := by omega
      rw [decimalDigits_of_ge h, decimalValue_append_singleton, ih (n / 10) (by omega),
        digitValue_digitByte (n % 10) hmod]
      omega

theorem forall_isDigit_decimalDigits (n : Nat) : ∀ c ∈ decimalDigits n, IsDigit c := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro c hc
    by_cases h : n < 10
    · rw [decimalDigits_of_lt h] at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact isDigit_digitByte n h
      · cases hc
    · rw [decimalDigits_of_ge h] at hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih (n / 10) (by omega) c hc
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact isDigit_digitByte (n % 10) (by omega)
        · cases hc

theorem decimalDigits_head : ∀ n : Nat, 0 < n →
    ∃ d ds, decimalDigits n = d :: ds ∧ IsPositiveDigit d := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases h : n < 10
    · exact ⟨_, [], decimalDigits_of_lt h, isPositiveDigit_digitByte n h hn⟩
    · obtain ⟨d, ds, hds, hd⟩ := ih (n / 10) (by omega) (by omega)
      exact ⟨d, ds ++ [digitByte (n % 10)], by simp [decimalDigits_of_ge h, hds], hd⟩

/-- 自然数の 10 進表記は数値識別子である(先頭ゼロがない)。 -/
theorem numericIdentifier_decimalDigits (n : Nat) : NumericIdentifier (decimalDigits n) := by
  by_cases hn : n = 0
  · subst hn
    rw [decimalDigits_of_lt (n := 0) (by decide), digitByte_zero]
    exact .zero
  · obtain ⟨d, ds, hds, hd⟩ := decimalDigits_head n (by omega)
    have hall := forall_isDigit_decimalDigits n
    rw [hds] at hall ⊢
    cases ds with
    | nil => exact .positive hd
    | cons d' ds' =>
      exact .positiveDigits hd
        (Digits.of_forall _ (List.cons_ne_nil _ _)
          (fun c hc => hall c (List.mem_cons_of_mem _ hc)))

/-- 正の値から数字列を読み進めた結果の 10 進表記は、元の表記に数字列を続けたもの。 -/
theorem decimalDigits_foldl (s : List Byte) : ∀ acc : Nat, 0 < acc → (∀ c ∈ s, IsDigit c) →
    decimalDigits (s.foldl decimalStep acc) = decimalDigits acc ++ s := by
  induction s with
  | nil => intro acc _ _; simp
  | cons c cs ih =>
    intro acc hacc hall
    have hc : IsDigit c := hall c (by simp)
    have hlt := hc.digitValue_lt
    have hge : ¬ acc * 10 + digitValue c < 10 := by omega
    have e₁ : (acc * 10 + digitValue c) / 10 = acc := by omega
    have e₂ : (acc * 10 + digitValue c) % 10 = digitValue c := by omega
    have hstep : decimalDigits (decimalStep acc c) = decimalDigits acc ++ [c] := by
      unfold decimalStep
      rw [decimalDigits_of_ge hge, e₁, e₂, hc.digitByte_digitValue]
    have hpos : 0 < decimalStep acc c := by unfold decimalStep; omega
    rw [List.foldl_cons, ih (decimalStep acc c) hpos
      (fun x hx => hall x (List.mem_cons_of_mem _ hx)), hstep]
    simp

theorem decimalDigits_decimalValue_cons {d : Byte} {ds : List Byte}
    (hd : IsPositiveDigit d) (hds : ∀ c ∈ ds, IsDigit c) :
    decimalDigits (decimalValue (d :: ds)) = d :: ds := by
  have e : decimalValue (d :: ds) = ds.foldl decimalStep (digitValue d) := by
    simp [decimalValue, decimalStep]
  have h := decimalDigits_foldl ds (digitValue d) hd.digitValue_pos hds
  rw [decimalDigits_of_lt hd.isDigit.digitValue_lt, hd.isDigit.digitByte_digitValue] at h
  rw [e]
  exact h

/-- 数値識別子を読んでから 10 進表記にすると元の数字列に戻る。 -/
theorem NumericIdentifier.decimalDigits_decimalValue {s : List Byte} (h : NumericIdentifier s) :
    decimalDigits (decimalValue s) = s := by
  cases h with
  | zero =>
    have e : decimalValue [Ascii.zero] = 0 := by decide
    rw [e, decimalDigits_of_lt (n := 0) (by decide), digitByte_zero]
  | positive hd => exact decimalDigits_decimalValue_cons hd (by simp)
  | positiveDigits hd hds => exact decimalDigits_decimalValue_cons hd hds.forall_isDigit

/-! ## プレリリース識別子 -/

/-- プレリリース識別子の値を表すバイト列。 -/
def PreReleaseId.toBytes : PreReleaseId → List Byte
  | .numeric n => decimalDigits n
  | .alphanumeric s => s

theorem PreReleaseId.ofBytes_of_digits {i : List Byte} (h : ∀ c ∈ i, IsDigit c) :
    PreReleaseId.ofBytes i = .numeric (decimalValue i) := ite_eq_left h

theorem PreReleaseId.ofBytes_of_not_digits {i : List Byte} (h : ¬ ∀ c ∈ i, IsDigit c) :
    PreReleaseId.ofBytes i = .alphanumeric i := ite_eq_right h

theorem AlphanumericIdentifier.not_forall_isDigit {s : List Byte}
    (h : AlphanumericIdentifier s) : ¬ ∀ c ∈ s, IsDigit c := by
  obtain ⟨c, hc, hnd⟩ := h.exists_isNonDigit
  exact fun hall => hnd.not_isDigit (hall c hc)

theorem PreReleaseIdentifier.ofBytes_wf {i : List Byte} (h : PreReleaseIdentifier i) :
    (PreReleaseId.ofBytes i).WF := by
  cases h with
  | alphanumeric ha =>
    rw [PreReleaseId.ofBytes_of_not_digits ha.not_forall_isDigit]
    exact ha
  | numeric hn =>
    rw [PreReleaseId.ofBytes_of_digits hn.forall_isDigit]
    exact True.intro

theorem PreReleaseIdentifier.toBytes_ofBytes {i : List Byte} (h : PreReleaseIdentifier i) :
    (PreReleaseId.ofBytes i).toBytes = i := by
  cases h with
  | alphanumeric ha =>
    exact congrArg PreReleaseId.toBytes (PreReleaseId.ofBytes_of_not_digits ha.not_forall_isDigit)
  | numeric hn =>
    exact (congrArg PreReleaseId.toBytes (PreReleaseId.ofBytes_of_digits hn.forall_isDigit)).trans
      hn.decimalDigits_decimalValue

theorem PreReleaseId.WF.toBytes_wf : ∀ {x : PreReleaseId}, x.WF → PreReleaseIdentifier x.toBytes
  | .numeric n, _ => .numeric (numericIdentifier_decimalDigits n)
  | .alphanumeric _, h => .alphanumeric h

theorem PreReleaseId.WF.ofBytes_toBytes :
    ∀ {x : PreReleaseId}, x.WF → PreReleaseId.ofBytes x.toBytes = x
  | .numeric n, _ =>
    (PreReleaseId.ofBytes_of_digits (forall_isDigit_decimalDigits n)).trans
      (congrArg PreReleaseId.numeric (decimalValue_decimalDigits n))
  | .alphanumeric _, h =>
    PreReleaseId.ofBytes_of_not_digits (AlphanumericIdentifier.not_forall_isDigit h)

/-! ## バージョン全体 -/

/-- バージョンの値を表す構成要素。 -/
def Version.toComponents (v : Version) : Components where
  major := decimalDigits v.major
  minor := decimalDigits v.minor
  patch := decimalDigits v.patch
  preRelease := v.preRelease.map PreReleaseId.toBytes
  build := v.build

theorem map_map_eq_self {α β : Type} {f : α → β} {g : β → α} :
    ∀ l : List α, (∀ x ∈ l, g (f x) = x) → (l.map f).map g = l
  | [], _ => rfl
  | x :: xs, h => by
    have ih := map_map_eq_self xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    show g (f x) :: (xs.map f).map g = x :: xs
    rw [h x (by simp), ih]

/-- 妥当な構成要素が表すバージョンは妥当。 -/
theorem Components.WF.toVersion_wf {c : Components} (h : c.WF) : c.toVersion.WF where
  preRelease := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact (h.preRelease i hi).ofBytes_wf
  build := h.build

/-- 妥当な構成要素は、表すバージョンから復元できる。 -/
theorem Components.WF.toComponents_toVersion {c : Components} (h : c.WF) :
    c.toVersion.toComponents = c := by
  rcases c with ⟨M, m, p, pre, build⟩
  have hM : NumericIdentifier M := h.major
  have hm : NumericIdentifier m := h.minor
  have hp : NumericIdentifier p := h.patch
  have hpre : ∀ i ∈ pre, PreReleaseIdentifier i := h.preRelease
  show Components.mk (decimalDigits (decimalValue M)) (decimalDigits (decimalValue m))
    (decimalDigits (decimalValue p))
    ((pre.map PreReleaseId.ofBytes).map PreReleaseId.toBytes) build = ⟨M, m, p, pre, build⟩
  rw [hM.decimalDigits_decimalValue, hm.decimalDigits_decimalValue,
    hp.decimalDigits_decimalValue,
    map_map_eq_self pre (fun i hi => (hpre i hi).toBytes_ofBytes)]

/-- 妥当なバージョンを表す構成要素は妥当。 -/
theorem Version.WF.toComponents_wf {v : Version} (h : v.WF) : v.toComponents.WF where
  major := numericIdentifier_decimalDigits _
  minor := numericIdentifier_decimalDigits _
  patch := numericIdentifier_decimalDigits _
  preRelease := fun i hi => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
    exact (h.preRelease x hx).toBytes_wf
  build := h.build

/-- 妥当なバージョンは、それを表す構成要素から復元できる。 -/
theorem Version.WF.toVersion_toComponents {v : Version} (h : v.WF) :
    v.toComponents.toVersion = v := by
  rcases v with ⟨M, m, p, pre, build⟩
  have hpre : ∀ x ∈ pre, x.WF := h.preRelease
  show Version.mk (decimalValue (decimalDigits M)) (decimalValue (decimalDigits m))
    (decimalValue (decimalDigits p))
    ((pre.map PreReleaseId.toBytes).map PreReleaseId.ofBytes) build = ⟨M, m, p, pre, build⟩
  rw [decimalValue_decimalDigits, decimalValue_decimalDigits, decimalValue_decimalDigits,
    map_map_eq_self pre (fun x hx => (hpre x hx).ofBytes_toBytes)]

end SemVer.Spec
