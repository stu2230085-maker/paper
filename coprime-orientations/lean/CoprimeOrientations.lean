/-!
# Coprime Orientations of Graphs

Machine-checked formalization of the main arithmetic, structural, and
gadget-theoretic theorems from the paper:
  "Coprime Orientations of Graphs: Structural Characterizations,
   Number-Theoretic Obstructions, and Complexity Dichotomy".

Zero external dependencies (pure Lean 4 core) and zero `sorry`s.
-/

namespace CoprimeOrientations

/-! ## Section 1: Basic Coprime Out-Degree Predicate and Equivalences -/

/-- An integer `k` is a valid coprime out-degree for a vertex of degree `d`
    if `k ≤ d` and `gcd(k, d - k) = 1`. -/
def IsCoprimeOut (d k : Nat) : Prop :=
  k ≤ d ∧ Nat.gcd k (d - k) = 1

/-- Equivalence between `gcd(k, d - k) = 1` and `gcd(k, d) = 1` for `k ≤ d`. -/
theorem gcd_sub_eq_gcd {d k : Nat} (h : k ≤ d) : Nat.gcd k (d - k) = Nat.gcd k d := by
  have hsum : k + (d - k) = d := Nat.add_sub_of_le h
  conv => rhs; rw [← hsum, Nat.add_comm]
  rw [Nat.gcd_add_self_right]

theorem isCoprimeOut_iff_gcd_deg {d k : Nat} :
    IsCoprimeOut d k ↔ k ≤ d ∧ Nat.gcd k d = 1 := by
  constructor
  · rintro ⟨hle, hgcd⟩
    exact ⟨hle, by rw [← gcd_sub_eq_gcd hle]; exact hgcd⟩
  · rintro ⟨hle, hgcd⟩
    exact ⟨hle, by rw [gcd_sub_eq_gcd hle]; exact hgcd⟩

/-- Reversal symmetry: `k ∈ A(d) ↔ d - k ∈ A(d)`. -/
theorem isCoprimeOut_rev {d k : Nat} (h : k ≤ d) :
    IsCoprimeOut d k ↔ IsCoprimeOut d (d - k) := by
  unfold IsCoprimeOut
  have hsub : d - (d - k) = k := Nat.sub_sub_self h
  constructor
  · rintro ⟨_, hgcd⟩
    exact ⟨Nat.sub_le d k, by rw [hsub, Nat.gcd_comm]; exact hgcd⟩
  · rintro ⟨_, hgcd⟩
    exact ⟨h, by rw [hsub, Nat.gcd_comm] at hgcd; exact hgcd⟩

/-- Isolated vertices (`d = 0`) never admit a coprime out-degree. -/
theorem not_isCoprimeOut_zero_deg (k : Nat) : ¬ IsCoprimeOut 0 k := by
  rintro ⟨hle, hgcd⟩
  have hk : k = 0 := Nat.le_zero.mp hle
  subst hk
  simp at hgcd

/-- Vertices of degree `d ≥ 2` cannot be sources (`k = 0`) or sinks (`k = d`). -/
theorem not_isCoprimeOut_zero_and_self {d : Nat} (hd : d ≥ 2) :
    ¬ IsCoprimeOut d 0 ∧ ¬ IsCoprimeOut d d := by
  constructor
  · rintro ⟨_, hgcd⟩
    simp at hgcd
    omega
  · rintro ⟨_, hgcd⟩
    simp at hgcd
    omega

theorem isCoprimeOut_one (k : Nat) : IsCoprimeOut 1 k ↔ k = 0 ∨ k = 1 := by
  unfold IsCoprimeOut
  constructor
  · rintro ⟨hle, _⟩; omega
  · rintro (rfl | rfl) <;> simp

theorem isCoprimeOut_two (k : Nat) : IsCoprimeOut 2 k ↔ k = 1 := by
  unfold IsCoprimeOut
  constructor
  · rintro ⟨hle, hgcd⟩
    match k with
    | 0 => simp at hgcd
    | 1 => rfl
    | 2 => simp at hgcd
    | _ + 3 => omega
  · rintro rfl; simp

theorem isCoprimeOut_three (k : Nat) : IsCoprimeOut 3 k ↔ k = 1 ∨ k = 2 := by
  unfold IsCoprimeOut
  constructor
  · rintro ⟨hle, hgcd⟩
    match k with
    | 0 => simp at hgcd
    | 1 => left; rfl
    | 2 => right; rfl
    | 3 => simp at hgcd
    | _ + 4 => omega
  · rintro (rfl | rfl) <;> simp

theorem isCoprimeOut_four (k : Nat) : IsCoprimeOut 4 k ↔ k = 1 ∨ k = 3 := by
  unfold IsCoprimeOut
  constructor
  · rintro ⟨hle, hgcd⟩
    match k with
    | 0 => simp at hgcd
    | 1 => left; rfl
    | 2 => simp at hgcd
    | 3 => right; rfl
    | 4 => simp at hgcd
    | _ + 5 => omega
  · rintro (rfl | rfl) <;> simp

theorem isCoprimeOut_six (k : Nat) : IsCoprimeOut 6 k ↔ k = 1 ∨ k = 5 := by
  unfold IsCoprimeOut
  constructor
  · rintro ⟨hle, hgcd⟩
    match k with
    | 0 => simp at hgcd
    | 1 => left; rfl
    | 2 => simp at hgcd
    | 3 => simp at hgcd
    | 4 => simp at hgcd
    | 5 => right; rfl
    | 6 => simp at hgcd
    | _ + 7 => omega
  · rintro (rfl | rfl) <;> simp

/-- For any positive even degree `d`, every coprime out-degree is odd. -/
theorem odd_of_isCoprimeOut_even {d k : Nat} (hd : d % 2 = 0) (h : IsCoprimeOut d k) :
    k % 2 = 1 := by
  rw [isCoprimeOut_iff_gcd_deg] at h
  have h2dvd : ¬ (2 ∣ k) := by
    intro h2k
    have h2d : 2 ∣ d := Nat.dvd_of_mod_eq_zero hd
    have h2g : 2 ∣ Nat.gcd k d := Nat.dvd_gcd h2k h2d
    rw [h.2] at h2g
    omega
  omega

/-- Balanced orientation arithmetic for odd degrees: `gcd(m, m + 1) = 1`. -/
theorem gcd_self_succ (m : Nat) : Nat.gcd m (m + 1) = 1 := by
  rw [Nat.add_comm, Nat.gcd_add_self_right, Nat.gcd_one_right]

theorem coprime_balanced_odd (m : Nat) :
    IsCoprimeOut (2 * m + 1) m ∧ IsCoprimeOut (2 * m + 1) (m + 1) := by
  constructor
  · refine ⟨by omega, ?_⟩
    have hsub : 2 * m + 1 - m = m + 1 := by omega
    rw [hsub]
    exact gcd_self_succ m
  · refine ⟨by omega, ?_⟩
    have hsub : 2 * m + 1 - (m + 1) = m := by omega
    rw [hsub, Nat.gcd_comm]
    exact gcd_self_succ m

/-- For every `d ≥ 1`, both `1` and `d - 1` are valid coprime out-degrees. -/
theorem coprime_one_and_pred {d : Nat} (hd : d ≥ 1) :
    IsCoprimeOut d 1 ∧ IsCoprimeOut d (d - 1) := by
  have h1 : IsCoprimeOut d 1 := by
    rw [isCoprimeOut_iff_gcd_deg]
    exact ⟨hd, Nat.gcd_one_left d⟩
  exact ⟨h1, (isCoprimeOut_rev hd).mp h1⟩

/-! ## Section 2: Powers of 2 Characterization -/

private theorem gcd_two_pow_eq_one_of_odd : ∀ (m k : Nat), k % 2 = 1 → Nat.gcd k (2 ^ m) = 1
  | 0, k, _ => by simp
  | m + 1, k, hodd => by
    have h1 : Nat.gcd k 2 = 1 := by
      have hle : Nat.gcd k 2 ≤ 2 := Nat.gcd_le_right k (by omega)
      have hdvd2 : Nat.gcd k 2 ∣ 2 := Nat.gcd_dvd_right k 2
      have hdvdk : Nat.gcd k 2 ∣ k := Nat.gcd_dvd_left k 2
      match hg : Nat.gcd k 2 with
      | 0 => rw [hg] at hdvd2; simp at hdvd2
      | 1 => rfl
      | 2 => rw [hg] at hdvdk; omega
      | _ + 3 => omega
    have hih := gcd_two_pow_eq_one_of_odd m k hodd
    have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
    rw [hpow]
    exact Nat.Coprime.mul_right hih h1

theorem isCoprimeOut_pow_two {m k : Nat} (hm : m ≥ 1) :
    IsCoprimeOut (2 ^ m) k ↔ k ≤ 2 ^ m ∧ k % 2 = 1 := by
  rw [isCoprimeOut_iff_gcd_deg]
  constructor
  · rintro ⟨hle, hgcd⟩
    refine ⟨hle, ?_⟩
    have heven : (2 ^ m) % 2 = 0 := by
      have : 2 ∣ 2 ^ m := by
        cases m with
        | zero => omega
        | succ m' => rw [Nat.pow_succ]; exact Nat.dvd_mul_left 2 (2 ^ m')
      exact Nat.mod_eq_zero_of_dvd this
    exact odd_of_isCoprimeOut_even heven (isCoprimeOut_iff_gcd_deg.mpr ⟨hle, hgcd⟩)
  · rintro ⟨hle, hodd⟩
    exact ⟨hle, gcd_two_pow_eq_one_of_odd m k hodd⟩

/-! ## Section 3: Uniqueness of the Mod-4 Obstruction at d = 6 -/

theorem six_all_mod4_eq_one {k : Nat} (h : IsCoprimeOut 6 k) : k % 4 = 1 := by
  rw [isCoprimeOut_six] at h
  rcases h with rfl | rfl <;> decide

private theorem gcd_two_mul_sub_one {m : Nat} (hm : m ≥ 1) : Nat.gcd (2 * m - 1) (4 * m) = 1 := by
  have h1 : Nat.gcd (2 * m - 1) 2 = 1 :=
    gcd_two_pow_eq_one_of_odd 1 (2 * m - 1) (by omega)
  have h2 : Nat.gcd (2 * m - 1) (2 * m) = 1 := by
    have heq : 2 * m = (2 * m - 1) + 1 := by omega
    conv => lhs; arg 2; rw [heq]
    exact gcd_self_succ (2 * m - 1)
  have h4 : 4 * m = 2 * (2 * m) := by omega
  rw [h4]
  exact Nat.Coprime.mul_right h1 h2

private theorem gcd_two_mul_add_one (m : Nat) : Nat.gcd (2 * m + 1) (4 * m) = 1 := by
  have h1 : Nat.gcd (2 * m + 1) 2 = 1 := gcd_two_pow_eq_one_of_odd 1 (2 * m + 1) (by omega)
  have h2 : Nat.gcd (2 * m + 1) (2 * m) = 1 := by
    rw [Nat.gcd_comm]
    exact gcd_self_succ (2 * m)
  have h4 : 4 * m = 2 * (2 * m) := by omega
  rw [h4]
  exact Nat.Coprime.mul_right h1 h2

private theorem gcd_sub_two_double_odd {M : Nat} (hM : M ≥ 3) (hodd : M % 2 = 1) :
    Nat.gcd (M - 2) (2 * M) = 1 := by
  have h2 : Nat.gcd (M - 2) 2 = 1 := gcd_two_pow_eq_one_of_odd 1 (M - 2) (by omega)
  have hM' : Nat.gcd (M - 2) M = 1 := by
    have heq : M = 2 + (M - 2) := by omega
    conv => lhs; arg 2; rw [heq]
    rw [Nat.gcd_add_self_right]
    exact h2
  exact Nat.Coprime.mul_right h2 hM'

private theorem gcd_add_two_double_odd {M : Nat} (hodd : M % 2 = 1) :
    Nat.gcd (M + 2) (2 * M) = 1 := by
  have h2 : Nat.gcd (M + 2) 2 = 1 := gcd_two_pow_eq_one_of_odd 1 (M + 2) (by omega)
  have hM' : Nat.gcd (M + 2) M = 1 := by
    rw [Nat.gcd_comm, Nat.add_comm, Nat.gcd_add_self_right]
    exact gcd_two_pow_eq_one_of_odd 1 M hodd
  exact Nat.Coprime.mul_right h2 hM'

private theorem gcd_sub_four_double_odd {M : Nat} (hM : M ≥ 5) (hodd : M % 2 = 1) :
    Nat.gcd (M - 4) (2 * M) = 1 := by
  have h2 : Nat.gcd (M - 4) 2 = 1 := gcd_two_pow_eq_one_of_odd 1 (M - 4) (by omega)
  have h4 : Nat.gcd (M - 4) 4 = 1 := gcd_two_pow_eq_one_of_odd 2 (M - 4) (by omega)
  have hM' : Nat.gcd (M - 4) M = 1 := by
    have heq : M = 4 + (M - 4) := by omega
    conv => lhs; arg 2; rw [heq]
    rw [Nat.gcd_add_self_right]
    exact h4
  exact Nat.Coprime.mul_right h2 hM'

/-- Theorem 4.2(a): For every even `d ≥ 4` with `d ≠ 6`, `A(d)` contains two elements
    differing by `2` (so `gcd{x - y : x, y ∈ A(d)} = 2`, whereas for `d = 6` it is `4`). -/
theorem even_ne_six_has_diff_two {d : Nat} (hd : d ≥ 4) (heven : d % 2 = 0) (hne6 : d ≠ 6) :
    ∃ x, IsCoprimeOut d x ∧ IsCoprimeOut d (x + 2) := by
  by_cases hmod4 : d % 4 = 0
  · let m := d / 4
    have hm : m ≥ 1 := by omega
    have hdm : d = 4 * m := by omega
    refine ⟨2 * m - 1, ?_, ?_⟩
    · rw [isCoprimeOut_iff_gcd_deg, hdm]
      exact ⟨by omega, gcd_two_mul_sub_one hm⟩
    · rw [isCoprimeOut_iff_gcd_deg, hdm]
      have hplus : 2 * m - 1 + 2 = 2 * m + 1 := by omega
      rw [hplus]
      exact ⟨by omega, gcd_two_mul_add_one m⟩
  · let M := d / 2
    have hModd : M % 2 = 1 := by omega
    have hMge5 : M ≥ 5 := by omega
    have hdM : d = 2 * M := by omega
    refine ⟨M - 4, ?_, ?_⟩
    · rw [isCoprimeOut_iff_gcd_deg, hdM]
      exact ⟨by omega, gcd_sub_four_double_odd hMge5 hModd⟩
    · rw [isCoprimeOut_iff_gcd_deg, hdM]
      have hplus : M - 4 + 2 = M - 2 := by omega
      rw [hplus]
      exact ⟨by omega, gcd_sub_two_double_odd (by omega) hModd⟩

/-! ## Section 4: The Prime-Power Gap Dichotomy (Theorem 5.1) -/

def IsPrime (p : Nat) : Prop :=
  p ≥ 2 ∧ ∀ a, a ∣ p → a = 1 ∨ a = p

def IsPrimePowerOrOne (d : Nat) : Prop :=
  d = 1 ∨ ∃ p k, IsPrime p ∧ k ≥ 1 ∧ d = p ^ k

/-- `d` has a consecutive gap in `A(d)` if there exists `x` with `1 ≤ x` and `x + 1 < d`
    such that neither `x` nor `x + 1` is coprime to `d`. -/
def HasConsecutiveGap (d : Nat) : Prop :=
  ∃ x, 1 ≤ x ∧ x + 1 < d ∧ ¬ IsCoprimeOut d x ∧ ¬ IsCoprimeOut d (x + 1)

private theorem not_coprime_prime_pow_implies_prime_dvd {p k x : Nat}
    (hp : IsPrime p) (h : Nat.gcd x (p ^ k) ≠ 1) : p ∣ x := by
  have hgt : Nat.gcd x (p ^ k) ≥ 2 := by
    have hne0 : Nat.gcd x (p ^ k) ≠ 0 := by
      intro h0
      have hp0 : p ^ k = 0 := (Nat.gcd_eq_zero_iff.mp h0).2
      have hpos : p ^ k > 0 := Nat.pow_pos (by have := hp.1; omega)
      omega
    omega
  let g := Nat.gcd x (p ^ k)
  have hg_dvd_x : g ∣ x := Nat.gcd_dvd_left x (p ^ k)
  have hg_dvd_pk : g ∣ p ^ k := Nat.gcd_dvd_right x (p ^ k)
  have hp_dvd_g : ∀ m, ∀ y, y ≥ 2 → y ∣ p ^ m → p ∣ y := by
    intro m
    induction m with
    | zero =>
      intro y hy hdvd
      simp at hdvd
      omega
    | succ m ih =>
      intro y hy hdvd
      rw [Nat.pow_succ] at hdvd
      by_cases hpy : p ∣ y
      · exact hpy
      · have hcop : Nat.gcd y p = 1 := by
          have hd : Nat.gcd y p ∣ p := Nat.gcd_dvd_right y p
          rcases hp.2 _ hd with h1 | h2
          · exact h1
          · exfalso; rw [← h2] at hpy; exact hpy (Nat.gcd_dvd_left y p)
        have hdvd' : y ∣ p ^ m := Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd
        exact ih y hy hdvd'
  exact Nat.dvd_trans (hp_dvd_g k g hgt hg_dvd_pk) hg_dvd_x

/-- Forward direction of Theorem 5.1: If `d = 1` or `d = p^k`, `A(d)` has no consecutive gap. -/
theorem no_consecutive_gap_of_prime_power {d : Nat} (h : IsPrimePowerOrOne d) :
    ¬ HasConsecutiveGap d := by
  rintro ⟨x, hx1, hxlt, hnx, hnx1⟩
  rcases h with rfl | ⟨p, k, hp, hk, rfl⟩
  · omega
  · have hgcd1 : Nat.gcd x (p ^ k) ≠ 1 := by
      intro hg; exact hnx (isCoprimeOut_iff_gcd_deg.mpr ⟨by omega, hg⟩)
    have hgcd2 : Nat.gcd (x + 1) (p ^ k) ≠ 1 := by
      intro hg; exact hnx1 (isCoprimeOut_iff_gcd_deg.mpr ⟨by omega, hg⟩)
    have hd1 : p ∣ x := not_coprime_prime_pow_implies_prime_dvd hp hgcd1
    have hd2 : p ∣ x + 1 := not_coprime_prime_pow_implies_prime_dvd hp hgcd2
    have hd_one : p ∣ 1 := by
      have : p ∣ (x + 1) - x := Nat.dvd_sub hd2 hd1
      simpa using this
    have := hp.1
    have := Nat.le_of_dvd (by omega) hd_one
    omega

/-- Helper: every `n ≥ 2` has a prime divisor. -/
private theorem exists_prime_dvd : ∀ n, n ≥ 2 → ∃ p, IsPrime p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hp : IsPrime n
    · exact ⟨n, hp, Nat.dvd_refl n⟩
    · unfold IsPrime at hp
      have hex : ∃ a, a ∣ n ∧ a ≠ 1 ∧ a ≠ n := by
        apply Classical.byContradiction
        intro hno
        apply hp
        refine ⟨hn, fun a ha => ?_⟩
        apply Classical.byContradiction
        intro hne
        exact hno ⟨a, ha, fun h1 => hne (Or.inl h1), fun h2 => hne (Or.inr h2)⟩
      rcases hex with ⟨a, hadvd, ha1, han⟩
      have ha_pos : a ≥ 1 := Nat.pos_of_dvd_of_pos hadvd (by omega)
      have ha_le : a ≤ n := Nat.le_of_dvd (by omega) hadvd
      have ha_lt : a < n := by omega
      have ha_ge2 : a ≥ 2 := by omega
      rcases ih a ha_lt ha_ge2 with ⟨p, hpp, hp_dvd_a⟩
      exact ⟨p, hpp, Nat.dvd_trans hp_dvd_a hadvd⟩

/-- Helper: if `d ≥ 2` is not a prime power, it factors as `d = u * v` with `u, v ≥ 2`
    and `gcd(u, v) = 1`. -/
private theorem coprime_split_of_not_prime_power :
    ∀ d, d ≥ 2 → ¬ IsPrimePowerOrOne d → ∃ u v, u ≥ 2 ∧ v ≥ 2 ∧ Nat.gcd u v = 1 ∧ d = u * v := by
  intro d hd hnot
  rcases exists_prime_dvd d hd with ⟨p, hp, hpdvd⟩
  have pull : ∀ m, m ≥ 1 → ∃ k v, m = p ^ k * v ∧ ¬ (p ∣ v) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro hm
      by_cases hpm : p ∣ m
      · rcases hpm with ⟨m', hm'⟩
        have hm'_pos : m' ≥ 1 := by
          cases m' with
          | zero => simp at hm'; omega
          | succ _ => omega
        have hm'_lt : m' < m := by
          have hp2 : 2 ≤ p := hp.1
          have hmul : 2 * m' ≤ p * m' := Nat.mul_le_mul_right m' hp2
          omega
        rcases ih m' hm'_lt hm'_pos with ⟨k, v, heq, hnd⟩
        refine ⟨k + 1, v, ?_, hnd⟩
        rw [hm', heq, Nat.pow_succ, Nat.mul_comm (p ^ k) p, Nat.mul_assoc]
      · exact ⟨0, m, by simp, hpm⟩
  rcases pull d (by omega) with ⟨k, v, hdv, hnd⟩
  have hk : k ≥ 1 := by
    cases k with
    | zero => simp at hdv; rw [← hdv] at hnd; exact absurd hpdvd hnd
    | succ _ => omega
  have hv_pos : v ≥ 1 := by
    cases v with
    | zero => simp at hdv; omega
    | succ _ => omega
  have hv_ne1 : v ≠ 1 := by
    intro hv1
    apply hnot
    right
    refine ⟨p, k, hp, hk, ?_⟩
    rw [hdv, hv1, Nat.mul_one]
  have hv_ge2 : v ≥ 2 := by omega
  have hu_ge2 : p ^ k ≥ 2 := by
    have hp2 : p ≥ 2 := hp.1
    cases k with
    | zero => omega
    | succ k' =>
      have hpos : 1 ≤ p ^ k' := Nat.pow_pos (by omega)
      rw [Nat.pow_succ]
      have h1 : 1 * p ≤ p ^ k' * p := Nat.mul_le_mul_right p hpos
      omega
  have hcop : Nat.gcd (p ^ k) v = 1 := by
    apply Classical.byContradiction
    intro hne1
    rw [Nat.gcd_comm] at hne1
    exact hnd (not_coprime_prime_pow_implies_prime_dvd hp hne1)
  exact ⟨p ^ k, v, hu_ge2, hv_ge2, hcop, hdv⟩

/-- Bezout's identity over `Int` proved directly by strong induction on `v`. -/
private theorem bezout_int : ∀ (u v : Nat), ∃ a b : Int, (Nat.gcd u v : Int) = u * a + v * b := by
  intro u v
  induction v using Nat.strongRecOn generalizing u with
  | ind v ih =>
    cases v with
    | zero =>
      refine ⟨1, 0, ?_⟩
      simp
    | succ v' =>
      let v := v' + 1
      have hmod_lt : u % v < v := Nat.mod_lt u (by omega)
      rcases ih (u % v) hmod_lt v with ⟨a, b, h⟩
      have hgcd : Nat.gcd u v = Nat.gcd v (u % v) := by
        rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]
      let q : Int := ((u / v : Nat) : Int)
      have hdiv : ((u % v : Nat) : Int) = (u : Int) - (v : Int) * q := by
        have hnat : v * (u / v) + u % v = u := Nat.div_add_mod u v
        have hcast : ((v * (u / v) + u % v : Nat) : Int) = (u : Int) := by exact_mod_cast hnat
        simp only [Int.natCast_add, Int.natCast_mul] at hcast
        change ((u % v : Nat) : Int) = (u : Int) - (v : Int) * ((u / v : Nat) : Int)
        omega
      refine ⟨b, a - b * q, ?_⟩
      rw [hgcd, h, hdiv]
      have hmul1 : ((u : Int) - (v : Int) * q) * b = (u : Int) * b - (v : Int) * q * b := Int.sub_mul _ _ _
      have hmul2 : (v : Int) * (a - b * q) = (v : Int) * a - (v : Int) * (b * q) := Int.mul_sub _ _ _
      have hassoc : (v : Int) * q * b = (v : Int) * (b * q) := by
        rw [Int.mul_assoc, Int.mul_comm q b]
      rw [hmul1, hmul2, hassoc]
      omega

/-- Helper: If `gcd(u, v) = 1` and `u, v ≥ 2`, there exists `x` with `1 ≤ x` and `x + 1 < u * v`
    such that `u ∣ x` and `v ∣ x + 1` (CRT). -/
private theorem exists_crt_consec {u v : Nat} (hu : u ≥ 2) (hv : v ≥ 2) (hcop : Nat.gcd u v = 1) :
    ∃ x, 1 ≤ x ∧ x + 1 < u * v ∧ u ∣ x ∧ v ∣ (x + 1) := by
  rcases bezout_int u v with ⟨a, b, hbez⟩
  rw [hcop] at hbez
  let r : Int := (-a) % (v : Int)
  have hr_nonneg : 0 ≤ r := Int.emod_nonneg (-a) (by omega)
  have hr_lt : r < (v : Int) := Int.emod_lt_of_pos (-a) (by omega)
  let t : Nat := r.toNat
  have ht_cast : (t : Int) = r := Int.toNat_of_nonneg hr_nonneg
  have ht_lt : t < v := by omega
  have hmod : ((u : Int) * (t : Int) + 1) % (v : Int) = 0 := by
    rw [ht_cast]
    have h1 : (u : Int) * ((-a) % (v : Int)) % (v : Int) = ((u : Int) * (-a)) % (v : Int) := by
      rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
    have h2 : (u : Int) * (-a) + 1 = (v : Int) * b := by
      have hneg : (u : Int) * (-a) = -((u : Int) * a) := Int.mul_neg _ _
      rw [hneg]
      omega
    calc ((u : Int) * ((-a) % (v : Int)) + 1) % (v : Int)
        = (((u : Int) * ((-a) % (v : Int))) % (v : Int) + 1 % (v : Int)) % (v : Int) := Int.add_emod _ _ _
      _ = (((u : Int) * (-a)) % (v : Int) + 1 % (v : Int)) % (v : Int) := by rw [h1]
      _ = ((u : Int) * (-a) + 1) % (v : Int) := (Int.add_emod _ _ _).symm
      _ = ((v : Int) * b) % (v : Int) := by rw [h2]
      _ = 0 := Int.mul_emod_right (v : Int) b
  have hv_dvd : v ∣ (u * t + 1) := by
    have hnat : (u * t + 1) % v = 0 := by
      have : ((u * t + 1 : Nat) : Int) % (v : Int) = 0 := by
        simpa [Int.natCast_add, Int.natCast_mul] using hmod
      omega
    exact Nat.dvd_of_mod_eq_zero hnat
  have ht_pos : t ≥ 1 := by
    by_cases ht0 : t = 0
    · rw [ht0] at hv_dvd
      have h1 : v ∣ 1 := by simpa using hv_dvd
      have := Nat.le_of_dvd (by omega) h1
      omega
    · omega
  refine ⟨u * t, ?_, ?_, Nat.dvd_mul_right u t, hv_dvd⟩
  · have : u * 1 ≤ u * t := Nat.mul_le_mul_left u ht_pos
    omega
  · have : u * t + u ≤ u * v := by
      have hle : t + 1 ≤ v := by omega
      have hmul := Nat.mul_le_mul_left u hle
      simpa [Nat.mul_add] using hmul
    omega

/-- Backward direction of Theorem 5.1: If `d ≥ 2` is not a prime power, `A(d)` has a consecutive gap. -/
theorem has_consecutive_gap_of_not_prime_power {d : Nat} (hd : d ≥ 2) (hnot : ¬ IsPrimePowerOrOne d) :
    HasConsecutiveGap d := by
  rcases coprime_split_of_not_prime_power d hd hnot with ⟨u, v, hu, hv, hcop, rfl⟩
  rcases exists_crt_consec hu hv hcop with ⟨x, hx1, hxlt, hux, hvx1⟩
  refine ⟨x, hx1, hxlt, ?_, ?_⟩
  · intro h
    rw [isCoprimeOut_iff_gcd_deg] at h
    have hdvd : u ∣ Nat.gcd x (u * v) := Nat.dvd_gcd hux (Nat.dvd_mul_right u v)
    rw [h.2] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro h
    rw [isCoprimeOut_iff_gcd_deg] at h
    have hdvd : v ∣ Nat.gcd (x + 1) (u * v) := Nat.dvd_gcd hvx1 (Nat.dvd_mul_left v u)
    rw [h.2] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega

/-- **Theorem 5.1 (Prime-Power Gap Dichotomy):**
    For every `d ≥ 1`, `A(d)` has no two consecutive missing integers in `[1, d - 1]`
    if and only if `d = 1` or `d = p^k` is a prime power. -/
theorem prime_power_gap_dichotomy {d : Nat} (hd : d ≥ 1) :
    ¬ HasConsecutiveGap d ↔ IsPrimePowerOrOne d := by
  constructor
  · intro hnogap
    by_cases h1 : d = 1
    · exact Or.inl h1
    · apply Classical.byContradiction
      intro hnot
      exact hnogap (has_consecutive_gap_of_not_prime_power (by omega) hnot)
  · exact no_consecutive_gap_of_prime_power

/-! ## Section 5: 5-Vertex 3-Way Equality Splitter Gadget (Theorem 5.3 Core Lemma) -/

def b2n (b : Bool) : Nat := if b then 1 else 0

def SplitterAdmits (e1 e2 e3 : Bool) : Prop :=
  ∃ (uw1 uw2 uw3 wv1 wv2 wv3 : Bool),
    IsCoprimeOut 2 (b2n (!uw1) + b2n wv1) ∧
    IsCoprimeOut 2 (b2n (!uw2) + b2n wv2) ∧
    IsCoprimeOut 2 (b2n (!uw3) + b2n wv3) ∧
    IsCoprimeOut 3 (b2n (!wv1) + b2n (!wv2) + b2n (!wv3)) ∧
    IsCoprimeOut 6 (b2n e1 + b2n e2 + b2n e3 + b2n uw1 + b2n uw2 + b2n uw3)

/-- **Lemma 5.4 (Splitter Gadget Characterization):**
    The 5-vertex splitter gadget admits a coprime orientation if and only if
    all three external edges have the same orientation (`e1 = e2 ∧ e2 = e3`). -/
theorem splitter_gadget_iff (e1 e2 e3 : Bool) :
    SplitterAdmits e1 e2 e3 ↔ (e1 = e2 ∧ e2 = e3) := by
  constructor
  · rintro ⟨uw1, uw2, uw3, wv1, wv2, wv3, hw1, hw2, hw3, hv, hu⟩
    rw [isCoprimeOut_two] at hw1 hw2 hw3
    rw [isCoprimeOut_three] at hv
    rw [isCoprimeOut_six] at hu
    cases e1 <;> cases e2 <;> cases e3 <;>
    cases uw1 <;> cases uw2 <;> cases uw3 <;>
    cases wv1 <;> cases wv2 <;> cases wv3 <;>
    simp [b2n] at hw1 hw2 hw3 hv hu ⊢
  · rintro ⟨h12, h23⟩
    subst h12; subst h23
    cases e1
    · exact ⟨true, false, false, true, false, false,
             by simp [b2n, isCoprimeOut_two],
             by simp [b2n, isCoprimeOut_two],
             by simp [b2n, isCoprimeOut_two],
             by simp [b2n, isCoprimeOut_three],
             by simp [b2n, isCoprimeOut_six]⟩
    · exact ⟨true, true, false, true, true, false,
             by simp [b2n, isCoprimeOut_two],
             by simp [b2n, isCoprimeOut_two],
             by simp [b2n, isCoprimeOut_two],
             by simp [b2n, isCoprimeOut_three],
             by simp [b2n, isCoprimeOut_six]⟩

/-! ## Section 6: Finite Sums, Eulerian Parity & 6-Regular Cut Obstruction -/

def finSum {n : Nat} (f : Fin n → Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => finSum (fun i : Fin n => f i.castSucc) + f (Fin.last n)

private theorem finSum_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    finSum f = finSum g := by
  have heq : f = g := funext h
  rw [heq]

private theorem finSum_const_zero : ∀ {n : Nat}, finSum (fun _ : Fin n => 0) = 0
  | 0 => rfl
  | n + 1 => by unfold finSum; dsimp; rw [finSum_const_zero]

private theorem finSum_const_one : ∀ {n : Nat}, finSum (fun _ : Fin n => 1) = n
  | 0 => rfl
  | n + 1 => by unfold finSum; dsimp; rw [finSum_const_one]

private theorem finSum_add {n : Nat} (f g : Fin n → Nat) :
    finSum (fun i => f i + g i) = finSum f + finSum g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold finSum
    dsimp
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

private theorem finSum_swap :
    ∀ {m n : Nat} (f : Fin m → Fin n → Nat),
      finSum (fun i => finSum (fun j => f i j)) = finSum (fun j => finSum (fun i => f i j))
  | 0, n, f => by
    have h0 : finSum (fun i : Fin 0 => finSum (fun j : Fin n => f i j)) = 0 := rfl
    rw [h0]
    have h1 : (fun j : Fin n => finSum (fun i : Fin 0 => f i j)) = (fun _ : Fin n => 0) := by
      funext j; rfl
    rw [h1, finSum_const_zero]
  | m + 1, n, f => by
    have hstep : finSum (fun i : Fin (m + 1) => finSum (fun j : Fin n => f i j)) =
        finSum (fun i : Fin m => finSum (fun j : Fin n => f i.castSucc j)) +
        finSum (fun j : Fin n => f (Fin.last m) j) := rfl
    rw [hstep, finSum_swap (fun i j => f i.castSucc j), ← finSum_add]
    apply finSum_congr
    intro j
    rfl

private theorem finSum_indicator_eq :
    ∀ {n : Nat} (k : Fin n), finSum (fun j : Fin n => if j = k then 1 else 0) = 1
  | 0, k => Fin.elim0 k
  | n + 1, k => by
    unfold finSum
    dsimp
    by_cases hk : k = Fin.last n
    · subst hk
      simp only [ite_true]
      have h0 : (fun j : Fin n => if j.castSucc = Fin.last n then 1 else 0) = (fun _ => 0) := by
        funext j
        have hne : j.castSucc ≠ Fin.last n := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        simp [hne]
      rw [h0, finSum_const_zero]
    · have hne_last : Fin.last n ≠ k := fun h => hk h.symm
      simp only [hne_last, ite_false, Nat.add_zero]
      have hklt : k.val < n := by
        have := k.isLt
        have : k.val ≠ n := fun h => hk (Fin.ext h)
        omega
      let k' : Fin n := ⟨k.val, hklt⟩
      have hcast : (fun j : Fin n => if j.castSucc = k then 1 else 0) =
          (fun j : Fin n => if j = k' then 1 else 0) := by
        funext j
        by_cases hjk : j = k'
        · subst hjk
          have heq : k'.castSucc = k := Fin.ext rfl
          simp [heq]
        · have hne : j.castSucc ≠ k := by
            intro heq
            have hv : j.castSucc.val = k.val := congrArg Fin.val heq
            exact hjk (Fin.ext hv)
          simp [hne, hjk]
      rw [hcast]
      exact finSum_indicator_eq k'

private theorem finSum_indicator_ne {n : Nat} (k : Fin n) :
    finSum (fun j : Fin n => if j = k then 0 else 1) = n - 1 := by
  have hadd : finSum (fun j : Fin n => (if j = k then 1 else 0) + (if j = k then 0 else 1)) =
      finSum (fun _ : Fin n => 1) := by
    apply finSum_congr; intro j; split <;> rfl
  rw [finSum_add, finSum_indicator_eq k, finSum_const_one] at hadd
  omega

private theorem finSum_mod_two_of_all_odd :
    ∀ {n : Nat} (f : Fin n → Nat), (∀ i, f i % 2 = 1) → finSum f % 2 = n % 2
  | 0, _, _ => rfl
  | n + 1, f, hodd => by
    unfold finSum
    have ih := finSum_mod_two_of_all_odd (fun i : Fin n => f i.castSucc) (fun i => hodd i.castSucc)
    have hlast := hodd (Fin.last n)
    omega

private theorem finSum_mod_four_of_all_mod4_one :
    ∀ {n : Nat} (f : Fin n → Nat), (∀ i, f i % 4 = 1) → finSum f % 4 = n % 4
  | 0, _, _ => rfl
  | n + 1, f, h1 => by
    unfold finSum
    have ih := finSum_mod_four_of_all_mod4_one (fun i : Fin n => f i.castSucc) (fun i => h1 i.castSucc)
    have hlast := h1 (Fin.last n)
    omega

/-- **Theorem 4.1 (Eulerian Parity Obstruction):**
    If every vertex `i ∈ Fin n` has even degree `deg i` and coprime out-degree `out i`,
    then `(∑ out) % 2 = n % 2`. -/
theorem eulerian_parity_obstruction {n : Nat} (deg out : Fin n → Nat)
    (heven : ∀ i, deg i % 2 = 0) (hcop : ∀ i, IsCoprimeOut (deg i) (out i)) :
    finSum out % 2 = n % 2 :=
  finSum_mod_two_of_all_odd out (fun i => odd_of_isCoprimeOut_even (heven i) (hcop i))

/-- **Theorem 4.2(b) (Cut Obstruction for 6-Regular Graphs):**
    If `S` is a subset of vertices of odd size `s` in a 6-regular graph with cut size `cut ∈ {0, 2}`,
    then no assignment of coprime out-degrees in `{1, 5}` can balance the cut equation. -/
theorem six_regular_cut_obstruction {s cut c : Nat}
    (hs_odd : s % 2 = 1) (hcut : cut = 0 ∨ cut = 2) (hc : c ≤ cut)
    (out : Fin s → Nat) (hcop : ∀ i, IsCoprimeOut 6 (out i)) :
    finSum out ≠ (6 * s - cut) / 2 + c := by
  intro heq
  have hmod4 := finSum_mod_four_of_all_mod4_one out (fun i => six_all_mod4_eq_one (hcop i))
  rw [heq] at hmod4
  rcases hcut with rfl | rfl <;> omega

/-! ## Section 7: Complete Bipartite Graphs K_{a, b} (Theorem 2.3(b)) -/

structure BipartiteOrientation (a b : Nat) where
  dir : Fin a → Fin b → Bool

def BipartiteOrientation.outU {a b : Nat} (O : BipartiteOrientation a b) (i : Fin a) : Nat :=
  finSum (fun j : Fin b => b2n (O.dir i j))

def BipartiteOrientation.outW {a b : Nat} (O : BipartiteOrientation a b) (j : Fin b) : Nat :=
  finSum (fun i : Fin a => b2n (!(O.dir i j)))

def IsCoprimeBipartite {a b : Nat} (O : BipartiteOrientation a b) : Prop :=
  (∀ i : Fin a, IsCoprimeOut b (O.outU i)) ∧
  (∀ j : Fin b, IsCoprimeOut a (O.outW j))

/-- **Theorem 2.3(b) (Universal Coprime Orientability of Complete Bipartite Graphs):**
    Every complete bipartite graph `K_{a, b}` (`a, b ≥ 1`) admits a coprime orientation. -/
theorem complete_bipartite_coprime {a b : Nat} (ha : a ≥ 1) (hb : b ≥ 1) :
    ∃ O : BipartiteOrientation a b, IsCoprimeBipartite O := by
  let O : BipartiteOrientation a b :=
    { dir := fun i j => (i.val == 0 && j.val != 0) || (i.val != 0 && j.val == 0) }
  let zA : Fin a := ⟨0, ha⟩
  let zB : Fin b := ⟨0, hb⟩
  refine ⟨O, ?_, ?_⟩
  · intro i
    unfold BipartiteOrientation.outU
    by_cases hi : i.val = 0
    · have hfun : (fun j : Fin b => b2n (O.dir i j)) = (fun j : Fin b => if j = zB then 0 else 1) := by
        funext j
        by_cases hj : j = zB
        · subst hj; simp [O, hi, zB, b2n]
        · have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
          simp [O, hi, hj, hj0, b2n]
      rw [hfun, finSum_indicator_ne zB]
      exact (coprime_one_and_pred hb).2
    · have hfun : (fun j : Fin b => b2n (O.dir i j)) = (fun j : Fin b => if j = zB then 1 else 0) := by
        funext j
        by_cases hj : j = zB
        · subst hj; simp [O, hi, zB, b2n]
        · have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
          simp [O, hi, hj, hj0, b2n]
      rw [hfun, finSum_indicator_eq zB]
      exact (coprime_one_and_pred hb).1
  · intro j
    unfold BipartiteOrientation.outW
    by_cases hj : j.val = 0
    · have hfun : (fun i : Fin a => b2n (!(O.dir i j))) = (fun i : Fin a => if i = zA then 1 else 0) := by
        funext i
        by_cases hi : i = zA
        · subst hi; simp [O, hj, zA, b2n]
        · have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
          simp [O, hi, hi0, hj, b2n]
      rw [hfun, finSum_indicator_eq zA]
      exact (coprime_one_and_pred ha).1
    · have hfun : (fun i : Fin a => b2n (!(O.dir i j))) = (fun i : Fin a => if i = zA then 0 else 1) := by
        funext i
        by_cases hi : i = zA
        · subst hi; simp [O, hj, zA, b2n]
        · have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
          simp [O, hi, hi0, hj, b2n]
      rw [hfun, finSum_indicator_ne zA]
      exact (coprime_one_and_pred ha).2

/-! ## Section 8: Complete Classification of Complete Graphs K_n (Theorem 3.1) -/

structure Tournament (n : Nat) where
  arc : Fin n → Fin n → Bool
  irrefl : ∀ i, arc i i = false
  antisym : ∀ i j, i ≠ j → arc i j = !arc j i

def Tournament.outDeg {n : Nat} (T : Tournament n) (i : Fin n) : Nat :=
  finSum (fun j : Fin n => b2n (T.arc i j))

def IsCoprimeTournament {n : Nat} (T : Tournament n) : Prop :=
  ∀ i : Fin n, IsCoprimeOut (n - 1) (T.outDeg i)

private theorem tournament_sum_outDeg_double {n : Nat} (T : Tournament n) :
    2 * finSum (fun i : Fin n => T.outDeg i) = n * (n - 1) := by
  have h1 : 2 * finSum (fun i => T.outDeg i) =
      finSum (fun i => T.outDeg i) + finSum (fun i => T.outDeg i) := by omega
  rw [h1]
  unfold Tournament.outDeg
  conv =>
    lhs
    arg 2
    rw [finSum_swap (fun i j => b2n (T.arc i j))]
  rw [← finSum_add]
  have hrow : ∀ i : Fin n,
      finSum (fun j : Fin n => b2n (T.arc i j)) + finSum (fun j : Fin n => b2n (T.arc j i)) = n - 1 := by
    intro i
    rw [← finSum_add]
    have hfun : (fun j : Fin n => b2n (T.arc i j) + b2n (T.arc j i)) =
        (fun j : Fin n => if j = i then 0 else 1) := by
      funext j
      by_cases hij : j = i
      · subst hij; simp [T.irrefl, b2n]
      · have ha := T.antisym i j (fun h => hij h.symm)
        rw [ha]
        cases T.arc j i <;> simp [b2n, hij]
    rw [hfun]
    exact finSum_indicator_ne i
  have htotal : (fun i : Fin n => finSum (fun j => b2n (T.arc i j)) + finSum (fun j => b2n (T.arc j i))) =
      (fun _ : Fin n => n - 1) := funext hrow
  rw [htotal]
  have hconst : ∀ {m : Nat} (c : Nat), finSum (fun _ : Fin m => c) = m * c := by
    intro m c
    induction m with
    | zero => simp [finSum]
    | succ m ih => unfold finSum; dsimp; rw [ih, Nat.succ_mul]
  exact hconst (n - 1)

/-- Necessity 1: `K_n` has no coprime orientation when `n ≡ 1 (mod 4)`. -/
theorem complete_graph_not_coprime_mod4_one {n : Nat} (hmod : n % 4 = 1) :
    ¬ ∃ T : Tournament n, IsCoprimeTournament T := by
  rintro ⟨T, hcop⟩
  have hsum := tournament_sum_outDeg_double T
  have heven : (n - 1) % 2 = 0 := by omega
  have hpar := eulerian_parity_obstruction (fun _ : Fin n => n - 1) T.outDeg
    (fun _ => heven) hcop
  have hn_mul : (n * (n - 1)) % 4 = 0 := by
    have h4 : 4 ∣ (n - 1) := Nat.dvd_of_mod_eq_zero (by omega)
    rcases h4 with ⟨k, hk⟩
    have : n * (n - 1) = 4 * (n * k) := by
      rw [hk, Nat.mul_left_comm]
    rw [this]
    exact Nat.mul_mod_right 4 (n * k)
  have hsum_eq : finSum T.outDeg = finSum (fun i => T.outDeg i) := rfl
  omega

/-- Necessity 2: `K_7` has no coprime orientation (Mod-4 obstruction). -/
theorem complete_graph_not_coprime_seven :
    ¬ ∃ T : Tournament 7, IsCoprimeTournament T := by
  rintro ⟨T, hcop⟩
  have hsum := tournament_sum_outDeg_double T
  have hmod4 := finSum_mod_four_of_all_mod4_one T.outDeg
    (fun i => six_all_mod4_eq_one (hcop i))
  have hsum_eq : finSum T.outDeg = finSum (fun i => T.outDeg i) := rfl
  omega

/-- Modular interval counting lemma: for `r < n` and `i < n`,
    the number of `j : Fin n` with `1 ≤ (j + n - i) % n ≤ r` is `r`. -/
private theorem finSum_mod_interval {n : Nat} (i : Fin n) :
    ∀ r, r < n →
      finSum (fun j : Fin n =>
        if 1 ≤ (j.val + n - i.val) % n ∧ (j.val + n - i.val) % n ≤ r then 1 else 0) = r
  | 0, _ => by
    have h0 : (fun j : Fin n =>
        if 1 ≤ (j.val + n - i.val) % n ∧ (j.val + n - i.val) % n ≤ 0 then 1 else 0) =
        (fun _ => 0) := by
      funext j
      split
      · omega
      · rfl
    rw [h0, finSum_const_zero]
  | r + 1, hr => by
    let target : Fin n := ⟨(i.val + (r + 1)) % n, Nat.mod_lt _ (by omega)⟩
    have hsplit :
        (fun j : Fin n =>
          if 1 ≤ (j.val + n - i.val) % n ∧ (j.val + n - i.val) % n ≤ r + 1 then 1 else 0) =
        (fun j : Fin n =>
          (if 1 ≤ (j.val + n - i.val) % n ∧ (j.val + n - i.val) % n ≤ r then 1 else 0) +
          (if j = target then 1 else 0)) := by
      funext j
      have huniq : (j.val + n - i.val) % n = r + 1 ↔ j = target := by
        constructor
        · intro heq
          apply Fin.ext
          have hi := i.isLt
          have hj := j.isLt
          change j.val = (i.val + (r + 1)) % n
          by_cases hji : i.val ≤ j.val
          · have h1 : (j.val + n - i.val) % n = j.val - i.val := by
              have : j.val + n - i.val = (j.val - i.val) + n := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [h1] at heq
            have : i.val + (r + 1) = j.val := by omega
            rw [this, Nat.mod_eq_of_lt hj]
          · have h1 : (j.val + n - i.val) % n = j.val + n - i.val :=
              Nat.mod_eq_of_lt (by omega)
            rw [h1] at heq
            have : i.val + (r + 1) = j.val + n := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
        · intro heq
          subst heq
          have hi := i.isLt
          change ((i.val + (r + 1)) % n + n - i.val) % n = r + 1
          by_cases hsum : i.val + (r + 1) < n
          · rw [Nat.mod_eq_of_lt hsum]
            have : i.val + (r + 1) + n - i.val = (r + 1) + n := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
          · have hsub : (i.val + (r + 1)) % n = i.val + (r + 1) - n := by
              have hlt : i.val + (r + 1) - n < n := by omega
              have hadd : i.val + (r + 1) = (i.val + (r + 1) - n) + n := by omega
              conv => lhs; rw [hadd]
              rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
            rw [hsub]
            have : i.val + (r + 1) - n + n - i.val = r + 1 := by omega
            rw [this, Nat.mod_eq_of_lt hr]
      by_cases hjt : j = target
      · have hmod := huniq.mpr hjt
        rw [hjt] at hmod
        simp [hjt, hmod]
      · have hmod : (j.val + n - i.val) % n ≠ r + 1 := fun h => hjt (huniq.mp h)
        by_cases hle : 1 ≤ (j.val + n - i.val) % n ∧ (j.val + n - i.val) % n ≤ r
        · have hle1 : 1 ≤ (j.val + n - i.val) % n ∧ (j.val + n - i.val) % n ≤ r + 1 := by omega
          simp [hjt, hle, hle1]
        · have hle1 : ¬ (1 ≤ (j.val + n - i.val) % n ∧ (j.val + n - i.val) % n ≤ r + 1) := by omega
          simp [hjt, hle, hle1]
    rw [hsplit, finSum_add, finSum_mod_interval i r (by omega), finSum_indicator_eq target]

/-- Sufficiency 1: `K_{2k}` (`k ≥ 1`) admits an explicit coprime tournament. -/
theorem complete_graph_coprime_even {k : Nat} (hk : k ≥ 1) :
    ∃ T : Tournament (2 * k), IsCoprimeTournament T := by
  let n := 2 * k
  let arcFn : Fin n → Fin n → Bool := fun i j =>
    let d := (j.val + n - i.val) % n
    (1 ≤ d && d ≤ k - 1) || (d == k && i.val < k)
  have hmod_opp : ∀ i j : Fin n, i ≠ j →
      (j.val + n - i.val) % n + (i.val + n - j.val) % n = n := by
    intro i j hne
    have hi := i.isLt
    have hj := j.isLt
    have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
    by_cases hlt : i.val < j.val
    · have h1 : (j.val + n - i.val) % n = j.val - i.val := by
        have : j.val + n - i.val = (j.val - i.val) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have h2 : (i.val + n - j.val) % n = i.val + n - j.val := Nat.mod_eq_of_lt (by omega)
      omega
    · have h1 : (j.val + n - i.val) % n = j.val + n - i.val := Nat.mod_eq_of_lt (by omega)
      have h2 : (i.val + n - j.val) % n = i.val - j.val := by
        have : i.val + n - j.val = (i.val - j.val) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
  let T : Tournament n :=
    { arc := arcFn
      irrefl := by
        intro i
        have hne : (0 : Nat) ≠ k := by omega
        simp [arcFn, hne]
      antisym := by
        intro i j hne
        have hopp := hmod_opp i j hne
        have hi := i.isLt
        have hj := j.isLt
        have hd1_pos : 1 ≤ (j.val + n - i.val) % n := by
          have : (i.val + n - j.val) % n < n := Nat.mod_lt _ (by omega)
          omega
        have hd2_pos : 1 ≤ (i.val + n - j.val) % n := by
          have : (j.val + n - i.val) % n < n := Nat.mod_lt _ (by omega)
          omega
        -- Case split on d1 = (j + n - i) % n vs k
        dsimp only [arcFn]
        by_cases hdk : (j.val + n - i.val) % n = k
        · have hd2k : (i.val + n - j.val) % n = k := by omega
          have hanti : (i.val < k) ↔ ¬ (j.val < k) := by
            by_cases hik : i.val < k
            · have h1 : (j.val + n - i.val) % n = k := hdk
              by_cases hji : i.val ≤ j.val
              · have : (j.val + n - i.val) % n = j.val - i.val := by
                  have : j.val + n - i.val = (j.val - i.val) + n := by omega
                  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                omega
              · have : (j.val + n - i.val) % n = j.val + n - i.val := Nat.mod_eq_of_lt (by omega)
                omega
            · by_cases hji : i.val ≤ j.val
              · have : (j.val + n - i.val) % n = j.val - i.val := by
                  have : j.val + n - i.val = (j.val - i.val) + n := by omega
                  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                omega
              · have : (j.val + n - i.val) % n = j.val + n - i.val := Nat.mod_eq_of_lt (by omega)
                omega
          by_cases hik : i.val < k
          · have hjk : ¬ (j.val < k) := hanti.mp hik
            have h1 : ¬ (k ≤ k - 1) := by omega
            simp [hdk, hd2k, hik, hjk, h1]
          · have hjk : j.val < k := by
              apply Classical.byContradiction; intro hnj; exact hik (hanti.mpr hnj)
            have h1 : ¬ (k ≤ k - 1) := by omega
            simp [hdk, hd2k, hik, hjk, h1]
        · by_cases hlt : (j.val + n - i.val) % n ≤ k - 1
          · have hgt : ¬ ((i.val + n - j.val) % n ≤ k - 1) := by omega
            have hne2 : (i.val + n - j.val) % n ≠ k := by omega
            simp [hd1_pos, hlt, hgt, hne2]
          · have hlt2 : (i.val + n - j.val) % n ≤ k - 1 := by omega
            simp [hd2_pos, hlt, hlt2, hdk] }
  refine ⟨T, ?_⟩
  intro i
  unfold Tournament.outDeg
  have hbase := finSum_mod_interval i (k - 1) (by omega)
  by_cases hik : i.val < k
  · let anti : Fin n := ⟨i.val + k, by omega⟩
    have hfun : (fun j : Fin n => b2n (T.arc i j)) =
        (fun j : Fin n =>
          (if 1 ≤ (j.val + n - i.val) % n ∧ (j.val + n - i.val) % n ≤ k - 1 then 1 else 0) +
          (if j = anti then 1 else 0)) := by
      funext j
      have huniq : (j.val + n - i.val) % n = k ↔ j = anti := by
        constructor
        · intro heq
          apply Fin.ext
          have hj := j.isLt
          change j.val = i.val + k
          by_cases hji : i.val ≤ j.val
          · have : (j.val + n - i.val) % n = j.val - i.val := by
              have : j.val + n - i.val = (j.val - i.val) + n := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            omega
          · have : (j.val + n - i.val) % n = j.val + n - i.val := Nat.mod_eq_of_lt (by omega)
            omega
        · intro heq; subst heq
          change (i.val + k + n - i.val) % n = k
          have : i.val + k + n - i.val = k + n := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      by_cases hja : j = anti
      · have hdk := huniq.mpr hja
        rw [hja] at hdk
        have hnotle : ¬ (k ≤ k - 1) := by omega
        simp [T, arcFn, b2n, hja, hdk, hik, hnotle]
      · have hne : (j.val + n - i.val) % n ≠ k := fun h => hja (huniq.mp h)
        by_cases hrange : 1 ≤ (j.val + n - i.val) % n ∧ (j.val + n - i.val) % n ≤ k - 1
        · simp [T, arcFn, b2n, hja, hrange]
        · simp [T, arcFn, b2n, hja, hne, hrange]
    rw [hfun, finSum_add, hbase, finSum_indicator_eq anti]
    have hdeg : n - 1 = 2 * (k - 1) + 1 := by omega
    have hout : k - 1 + 1 = (k - 1) + 1 := rfl
    rw [hdeg, hout]
    exact (coprime_balanced_odd (k - 1)).2
  · have hfun : (fun j : Fin n => b2n (T.arc i j)) =
        (fun j : Fin n =>
          if 1 ≤ (j.val + n - i.val) % n ∧ (j.val + n - i.val) % n ≤ k - 1 then 1 else 0) := by
      funext j
      by_cases hrange : 1 ≤ (j.val + n - i.val) % n ∧ (j.val + n - i.val) % n ≤ k - 1
      · simp [T, arcFn, b2n, hik, hrange]
      · simp [T, arcFn, b2n, hik, hrange]
    rw [hfun, hbase]
    have hdeg : n - 1 = 2 * (k - 1) + 1 := by omega
    rw [hdeg]
    exact (coprime_balanced_odd (k - 1)).1

/-- Sufficiency 2: `K_3` admits a coprime tournament (directed 3-cycle). -/
theorem complete_graph_coprime_three : ∃ T : Tournament 3, IsCoprimeTournament T := by
  let T : Tournament 3 :=
    { arc := fun i j => (j.val + 3 - i.val) % 3 == 1
      irrefl := by
        intro i
        match i with
        | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => simp
      antisym := by
        intro i j hne
        match i, j with
        | ⟨0, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩ => exact absurd rfl hne
        | ⟨0, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨2, _⟩
        | ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨2, _⟩
        | ⟨2, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨1, _⟩ => simp }
  refine ⟨T, ?_⟩
  intro i
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ =>
    simp [Tournament.outDeg, finSum, T, b2n, isCoprimeOut_two]

/-- Flip membership predicate for our explicit arc-reversal set `F` on `K_{2M+1}` (`M ≥ 5` odd):
    - `(0, 1), (0, 2), (0, 3), (0, 5)`
    - `(2M, 2), (2M, 3)`
    - `(2M - 2, 1), (2M - 2, 2M - 1)`
    - `(u, u + 1), (u, u + 3)` for even `u` with `4 ≤ u ≤ 2M - 4`. -/
private def inFlipSet (M u v : Nat) : Bool :=
  (u == 0 && (v == 1 || v == 2 || v == 3 || v == 5)) ||
  (u == 2 * M && (v == 2 || v == 3)) ||
  (u == 2 * M - 2 && (v == 1 || v == 2 * M - 1)) ||
  (4 ≤ u && u ≤ 2 * M - 4 && u % 2 == 0 && (v == u + 1 || v == u + 3))

/-- Helper: counting how many `j : Fin (2M+1)` satisfy `p j` when `p` matches 2 or 4 explicit indices. -/
private theorem finSum_two_distinct {n : Nat} (a b : Fin n) (hab : a ≠ b) :
    finSum (fun j : Fin n => if j = a ∨ j = b then 1 else 0) = 2 := by
  have hsplit : (fun j : Fin n => if j = a ∨ j = b then 1 else 0) =
      (fun j : Fin n => (if j = a then 1 else 0) + (if j = b then 1 else 0)) := by
    funext j
    by_cases hja : j = a
    · subst hja; simp [hab]
    · by_cases hjb : j = b
      · subst hjb; simp [Ne.symm hab]
      · simp [hja, hjb]
  rw [hsplit, finSum_add, finSum_indicator_eq a, finSum_indicator_eq b]

private theorem finSum_four_distinct {n : Nat} (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    finSum (fun j : Fin n => if j = a ∨ j = b ∨ j = c ∨ j = d then 1 else 0) = 4 := by
  have hsplit : (fun j : Fin n => if j = a ∨ j = b ∨ j = c ∨ j = d then 1 else 0) =
      (fun j : Fin n =>
        (if j = a ∨ j = b then 1 else 0) + (if j = c ∨ j = d then 1 else 0)) := by
    funext j
    by_cases hja : j = a
    · subst hja; simp [hac, had]
    · by_cases hjb : j = b
      · subst hjb; simp [hbc, hbd]
      · by_cases hjc : j = c
        · subst hjc; simp [hja, hjb]
        · by_cases hjd : j = d
          · subst hjd; simp [Ne.symm had, Ne.symm hbd]
          · simp [hja, hjb, hjc, hjd]
  rw [hsplit, finSum_add, finSum_two_distinct a b hab, finSum_two_distinct c d hcd]

/-- Sufficiency 3: `K_{2M+1}` (`M ≥ 5` odd) admits an explicit coprime tournament
    obtained from the circulant regular tournament `T_{2M+1}` by reversing `F`. -/
theorem complete_graph_coprime_odd_ge_eleven {M : Nat} (hM : M ≥ 5) (hodd : M % 2 = 1) :
    ∃ T : Tournament (2 * M + 1), IsCoprimeTournament T := by
  let n := 2 * M + 1
  let baseArc : Fin n → Fin n → Bool := fun i j =>
    let d := (j.val + n - i.val) % n
    1 ≤ d && d ≤ M
  -- Every arc in F is a forward arc of baseArc, and F is bipartite (L ∩ R = ∅) so F(u,v) → ¬F(v,u).
  have hF_in_base : ∀ i j : Fin n, inFlipSet M i.val j.val = true → baseArc i j = true := by
    intro i j hF
    have hi := i.isLt
    have hj := j.isLt
    simp only [inFlipSet, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hF
    dsimp only [baseArc]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rcases hF with (((⟨h0, ((h1 | h2) | h3) | h5⟩ | ⟨h2M, h2 | h3⟩) | ⟨h2M2, h1 | h2M1⟩) | ⟨⟨⟨hge, hle⟩, hev⟩, h1 | h3⟩)
    · -- (0, 1)
      rw [h0, h1]; have : (1 + n - 0) % n = 1 := by
        have : 1 + n - 0 = 1 + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · -- (0, 2)
      rw [h0, h2]; have : (2 + n - 0) % n = 2 := by
        have : 2 + n - 0 = 2 + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · -- (0, 3)
      rw [h0, h3]; have : (3 + n - 0) % n = 3 := by
        have : 3 + n - 0 = 3 + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · -- (0, 5)
      rw [h0, h5]; have : (5 + n - 0) % n = 5 := by
        have : 5 + n - 0 = 5 + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · -- (2M, 2)
      rw [h2M, h2]; have : (2 + n - 2 * M) % n = 3 := by
        have : 2 + n - 2 * M = 3 := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
      omega
    · -- (2M, 3)
      rw [h2M, h3]; have : (3 + n - 2 * M) % n = 4 := by
        have : 3 + n - 2 * M = 4 := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
      omega
    · -- (2M - 2, 1)
      rw [h2M2, h1]; have : (1 + n - (2 * M - 2)) % n = 4 := by
        have : 1 + n - (2 * M - 2) = 4 := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
      omega
    · -- (2M - 2, 2M - 1)
      rw [h2M2, h2M1]; have : (2 * M - 1 + n - (2 * M - 2)) % n = 1 := by
        have : 2 * M - 1 + n - (2 * M - 2) = 1 + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · -- (u, u + 1)
      rw [h1]; have : (i.val + 1 + n - i.val) % n = 1 := by
        have : i.val + 1 + n - i.val = 1 + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · -- (u, u + 3)
      rw [h3]; have : (i.val + 3 + n - i.val) % n = 3 := by
        have : i.val + 3 + n - i.val = 3 + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
  have hF_disj : ∀ i j : Fin n, inFlipSet M i.val j.val = true → inFlipSet M j.val i.val = false := by
    intro i j hF
    simp only [inFlipSet, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hF
    -- Left vertices of F are all even ≠ 2; right vertices are all odd or 2.
    have hL : i.val % 2 = 0 ∧ i.val ≠ 2 := by
      rcases hF with (((⟨h0, _⟩ | ⟨h2M, _⟩) | ⟨h2M2, _⟩) | ⟨⟨⟨hge, _⟩, hev⟩, _⟩) <;> omega
    have hR : j.val % 2 = 1 ∨ j.val = 2 := by
      rcases hF with (((⟨_, ((h1 | h2) | h3) | h5⟩ | ⟨_, h2 | h3⟩) | ⟨_, h1 | h2M1⟩) | ⟨⟨⟨_, _⟩, hev⟩, h1 | h3⟩) <;> omega
    cases hrev : inFlipSet M j.val i.val
    · rfl
    · simp only [inFlipSet, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrev
      have hLj : j.val % 2 = 0 ∧ j.val ≠ 2 := by
        rcases hrev with (((⟨h0, _⟩ | ⟨h2M, _⟩) | ⟨h2M2, _⟩) | ⟨⟨⟨hge, _⟩, hev⟩, _⟩) <;> omega
      omega
  have hbase_irrefl : ∀ i : Fin n, baseArc i i = false := by
    intro i
    simp [baseArc]
  have hbase_antisym : ∀ i j : Fin n, i ≠ j → baseArc i j = !baseArc j i := by
    intro i j hne
    have hi := i.isLt
    have hj := j.isLt
    have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have hopp : (j.val + n - i.val) % n + (i.val + n - j.val) % n = n := by
      by_cases hlt : i.val < j.val
      · have h1 : (j.val + n - i.val) % n = j.val - i.val := by
          have : j.val + n - i.val = (j.val - i.val) + n := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have h2 : (i.val + n - j.val) % n = i.val + n - j.val := Nat.mod_eq_of_lt (by omega)
        omega
      · have h1 : (j.val + n - i.val) % n = j.val + n - i.val := Nat.mod_eq_of_lt (by omega)
        have h2 : (i.val + n - j.val) % n = i.val - j.val := by
          have : i.val + n - j.val = (i.val - j.val) + n := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    have hd1_pos : 1 ≤ (j.val + n - i.val) % n := by
      have : (i.val + n - j.val) % n < n := Nat.mod_lt _ (by omega); omega
    have hd2_pos : 1 ≤ (i.val + n - j.val) % n := by
      have : (j.val + n - i.val) % n < n := Nat.mod_lt _ (by omega); omega
    dsimp only [baseArc]
    by_cases h1 : (j.val + n - i.val) % n ≤ M
    · have h2 : ¬ ((i.val + n - j.val) % n ≤ M) := by omega
      simp [hd1_pos, h1, h2]
    · have h2 : (i.val + n - j.val) % n ≤ M := by omega
      simp [hd2_pos, h1, h2]
  let arcFn : Fin n → Fin n → Bool := fun i j =>
    (baseArc i j && !inFlipSet M i.val j.val) || inFlipSet M j.val i.val
  let T : Tournament n :=
    { arc := arcFn
      irrefl := by
        intro i
        have hb := hbase_irrefl i
        have hF : inFlipSet M i.val i.val = false := by
          cases h : inFlipSet M i.val i.val
          · rfl
          · have := hF_in_base i i h; rw [hb] at this; contradiction
        simp [arcFn, hb, hF]
      antisym := by
        intro i j hne
        have ha := hbase_antisym i j hne
        dsimp only [arcFn]
        cases hFij : inFlipSet M i.val j.val
        · cases hFji : inFlipSet M j.val i.val
          · simp [ha]
          · have hbji := hF_in_base j i hFji
            have hbij : baseArc i j = false := by rw [ha, hbji]; rfl
            simp [hbji, hbij]
        · have hFji := hF_disj i j hFij
          have hbij := hF_in_base i j hFij
          have hbji : baseArc j i = false := by
            cases h : baseArc j i
            · rfl
            · rw [h] at ha; simp [hbij] at ha
          simp [hFji, hbij, hbji] }
  -- Key accounting identity for every vertex i:
  -- outDeg(i) + #{j : F(i, j)} = M + #{j : F(j, i)}
  have hdeg_eq : ∀ i : Fin n,
      T.outDeg i + finSum (fun j : Fin n => b2n (inFlipSet M i.val j.val)) =
      M + finSum (fun j : Fin n => b2n (inFlipSet M j.val i.val)) := by
    intro i
    unfold Tournament.outDeg
    have hMsum : finSum (fun j : Fin n => b2n (baseArc i j)) = M := by
      have hfun : (fun j : Fin n => b2n (baseArc i j)) =
          (fun j : Fin n => if 1 ≤ (j.val + n - i.val) % n ∧ (j.val + n - i.val) % n ≤ M then 1 else 0) := by
        funext j
        by_cases h : 1 ≤ (j.val + n - i.val) % n ∧ (j.val + n - i.val) % n ≤ M
        · simp [baseArc, b2n, h]
        · simp [baseArc, b2n, h]
      rw [hfun]
      exact finSum_mod_interval i M (by omega)
    calc finSum (fun j : Fin n => b2n (T.arc i j)) + finSum (fun j : Fin n => b2n (inFlipSet M i.val j.val))
        = finSum (fun j : Fin n => b2n (T.arc i j) + b2n (inFlipSet M i.val j.val)) := (finSum_add _ _).symm
      _ = finSum (fun j : Fin n => b2n (baseArc i j) + b2n (inFlipSet M j.val i.val)) := by
          apply finSum_congr
          intro j
          dsimp only [T, arcFn]
          cases hFij : inFlipSet M i.val j.val
          · cases hFji : inFlipSet M j.val i.val
            · simp [b2n]
            · have hbji := hF_in_base j i hFji
              have hne : i ≠ j := by
                intro heq; subst heq; rw [hbase_irrefl] at hbji; contradiction
              have hbij : baseArc i j = false := by rw [hbase_antisym i j hne, hbji]; rfl
              simp [hbij, b2n]
          · have hFji := hF_disj i j hFij
            have hbij := hF_in_base i j hFij
            simp [hFji, hbij, b2n]
      _ = finSum (fun j : Fin n => b2n (baseArc i j)) + finSum (fun j : Fin n => b2n (inFlipSet M j.val i.val)) := finSum_add _ _
      _ = M + finSum (fun j : Fin n => b2n (inFlipSet M j.val i.val)) := by rw [hMsum]
  -- Now verify outDeg(i) ∈ {M - 4, M - 2, M + 2} for all i : Fin n!
  refine ⟨T, ?_⟩
  intro i
  have hi := i.isLt
  have heq := hdeg_eq i
  have hdeg_n : n - 1 = 2 * M := by omega
  rw [hdeg_n]
  -- Split into L = {i : even ∧ i ≠ 2} and R = {i : odd ∨ i = 2}
  by_cases hL : i.val % 2 = 0 ∧ i.val ≠ 2
  · -- For i ∈ L, no j has inFlipSet M j i = true
    have hIn0 : finSum (fun j : Fin n => b2n (inFlipSet M j.val i.val)) = 0 := by
      have h0 : (fun j : Fin n => b2n (inFlipSet M j.val i.val)) = (fun _ => 0) := by
        funext j
        cases h : inFlipSet M j.val i.val
        · rfl
        · simp only [inFlipSet, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
          rcases h with (((⟨_, ((h1 | h2) | h3) | h5⟩ | ⟨_, h2 | h3⟩) | ⟨_, h1 | h2M1⟩) | ⟨⟨⟨_, _⟩, hev⟩, h1 | h3⟩) <;> omega
      rw [h0, finSum_const_zero]
    rw [hIn0, Nat.add_zero] at heq
    by_cases hi0 : i.val = 0
    · -- i = 0: out-flips are {1, 2, 3, 5} (count = 4) => outDeg = M - 4
      let j1 : Fin n := ⟨1, by omega⟩
      let j2 : Fin n := ⟨2, by omega⟩
      let j3 : Fin n := ⟨3, by omega⟩
      let j5 : Fin n := ⟨5, by omega⟩
      have hOut4 : finSum (fun j : Fin n => b2n (inFlipSet M i.val j.val)) = 4 := by
        have hfun : (fun j : Fin n => b2n (inFlipSet M i.val j.val)) =
            (fun j : Fin n => if j = j1 ∨ j = j2 ∨ j = j3 ∨ j = j5 then 1 else 0) := by
          funext j
          by_cases h : j = j1 ∨ j = j2 ∨ j = j3 ∨ j = j5
          · rcases h with rfl | rfl | rfl | rfl <;> simp [inFlipSet, hi0, j1, j2, j3, j5, b2n]
          · have h1 : j.val ≠ 1 := fun hv => h (Or.inl (Fin.ext hv))
            have h2 : j.val ≠ 2 := fun hv => h (Or.inr (Or.inl (Fin.ext hv)))
            have h3 : j.val ≠ 3 := fun hv => h (Or.inr (Or.inr (Or.inl (Fin.ext hv))))
            have h5 : j.val ≠ 5 := fun hv => h (Or.inr (Or.inr (Or.inr (Fin.ext hv))))
            have hne2M2 : (0 : Nat) ≠ 2 * M - 2 := by omega
            simp [inFlipSet, hi0, h, h1, h2, h3, h5, hne2M2, b2n]
        rw [hfun]
        exact finSum_four_distinct j1 j2 j3 j5
          (by intro h; have := congrArg Fin.val h; simp [j1, j2] at this)
          (by intro h; have := congrArg Fin.val h; simp [j1, j3] at this)
          (by intro h; have := congrArg Fin.val h; simp [j1, j5] at this)
          (by intro h; have := congrArg Fin.val h; simp [j2, j3] at this)
          (by intro h; have := congrArg Fin.val h; simp [j2, j5] at this)
          (by intro h; have := congrArg Fin.val h; simp [j3, j5] at this)
      have hout : T.outDeg i = M - 4 := by omega
      rw [hout, isCoprimeOut_iff_gcd_deg]
      exact ⟨by omega, gcd_sub_four_double_odd hM hodd⟩
    · -- i ∈ {4, 6, ..., 2M - 2, 2M}: out-flips have count 2 => outDeg = M - 2
      have hOut2 : finSum (fun j : Fin n => b2n (inFlipSet M i.val j.val)) = 2 := by
        by_cases hi2M : i.val = 2 * M
        · let a : Fin n := ⟨2, by omega⟩
          let b : Fin n := ⟨3, by omega⟩
          have hfun : (fun j : Fin n => b2n (inFlipSet M i.val j.val)) =
              (fun j : Fin n => if j = a ∨ j = b then 1 else 0) := by
            funext j
            by_cases h : j = a ∨ j = b
            · rcases h with rfl | rfl <;> simp [inFlipSet, hi2M, a, b, b2n]
            · have ha : j.val ≠ 2 := fun hv => h (Or.inl (Fin.ext hv))
              have hb : j.val ≠ 3 := fun hv => h (Or.inr (Fin.ext hv))
              have hne0 : 2 * M ≠ 0 := by omega
              have hne2M2 : 2 * M ≠ 2 * M - 2 := by omega
              have hnotle : ¬ (2 * M ≤ 2 * M - 4) := by omega
              simp [inFlipSet, hi2M, h, ha, hb, hne0, hne2M2, hnotle, b2n]
          rw [hfun]
          exact finSum_two_distinct a b (by intro h; have := congrArg Fin.val h; simp [a, b] at this)
        · by_cases hi2M2 : i.val = 2 * M - 2
          · let a : Fin n := ⟨1, by omega⟩
            let b : Fin n := ⟨2 * M - 1, by omega⟩
            have hfun : (fun j : Fin n => b2n (inFlipSet M i.val j.val)) =
                (fun j : Fin n => if j = a ∨ j = b then 1 else 0) := by
              funext j
              by_cases h : j = a ∨ j = b
              · rcases h with rfl | rfl <;> simp [inFlipSet, hi2M2, a, b, b2n]
              · have ha : j.val ≠ 1 := fun hv => h (Or.inl (Fin.ext hv))
                have hb : j.val ≠ 2 * M - 1 := fun hv => h (Or.inr (Fin.ext hv))
                have hne0 : 2 * M - 2 ≠ 0 := by omega
                have hne2M : 2 * M - 2 ≠ 2 * M := by omega
                have hnotle : ¬ (2 * M - 2 ≤ 2 * M - 4) := by omega
                simp [inFlipSet, hi2M2, h, ha, hb, hne0, hne2M, hnotle, b2n]
            rw [hfun]
            exact finSum_two_distinct a b (by intro h; have := congrArg Fin.val h; simp [a, b] at this; omega)
          · -- 4 ≤ i.val ≤ 2M - 4 and even
            have hge4 : 4 ≤ i.val := by omega
            have hle4 : i.val ≤ 2 * M - 4 := by omega
            let a : Fin n := ⟨i.val + 1, by omega⟩
            let b : Fin n := ⟨i.val + 3, by omega⟩
            have hfun : (fun j : Fin n => b2n (inFlipSet M i.val j.val)) =
                (fun j : Fin n => if j = a ∨ j = b then 1 else 0) := by
              funext j
              by_cases h : j = a ∨ j = b
              · rcases h with rfl | rfl <;> simp [inFlipSet, hge4, hle4, hL.1, a, b, b2n]
              · have ha : j.val ≠ i.val + 1 := fun hv => h (Or.inl (Fin.ext hv))
                have hb : j.val ≠ i.val + 3 := fun hv => h (Or.inr (Fin.ext hv))
                simp [inFlipSet, hi0, hi2M, hi2M2, hge4, hle4, hL.1, h, ha, hb, b2n]
            rw [hfun]
            exact finSum_two_distinct a b (by intro h; have := congrArg Fin.val h; simp [a, b] at this)
      have hout : T.outDeg i = M - 2 := by omega
      rw [hout, isCoprimeOut_iff_gcd_deg]
      exact ⟨by omega, gcd_sub_two_double_odd (by omega) hodd⟩
  · -- i ∈ R = {1, 2, 3, 5, 7, ..., 2M - 1}: no out-flips, exactly 2 in-flips => outDeg = M + 2
    have hR : i.val % 2 = 1 ∨ i.val = 2 := by omega
    have hOut0 : finSum (fun j : Fin n => b2n (inFlipSet M i.val j.val)) = 0 := by
      have h0 : (fun j : Fin n => b2n (inFlipSet M i.val j.val)) = (fun _ => 0) := by
        funext j
        cases h : inFlipSet M i.val j.val
        · rfl
        · simp only [inFlipSet, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
          rcases h with (((⟨h0, _⟩ | ⟨h2M, _⟩) | ⟨h2M2, _⟩) | ⟨⟨⟨hge, _⟩, hev⟩, _⟩) <;> omega
      rw [h0, finSum_const_zero]
    rw [hOut0, Nat.add_zero] at heq
    have hIn2 : finSum (fun j : Fin n => b2n (inFlipSet M j.val i.val)) = 2 := by
      by_cases hi1 : i.val = 1
      · let a : Fin n := ⟨0, by omega⟩
        let b : Fin n := ⟨2 * M - 2, by omega⟩
        have hfun : (fun j : Fin n => b2n (inFlipSet M j.val i.val)) =
            (fun j : Fin n => if j = a ∨ j = b then 1 else 0) := by
          funext j
          by_cases h : j = a ∨ j = b
          · rcases h with rfl | rfl <;> simp [inFlipSet, hi1, a, b, b2n]
          · have ha : j.val ≠ 0 := fun hv => h (Or.inl (Fin.ext hv))
            have hb : j.val ≠ 2 * M - 2 := fun hv => h (Or.inr (Fin.ext hv))
            have h1 : ¬ (4 ≤ j.val ∧ (1 = j.val + 1 ∨ 1 = j.val + 3)) := by omega
            cases hf : inFlipSet M j.val i.val
            · simp [h, b2n]
            · simp only [inFlipSet, hi1, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
              rcases hf with (((⟨h0, _⟩ | ⟨_, h2 | h3⟩) | ⟨h2M2, _⟩) | ⟨⟨⟨hge, _⟩, _⟩, hc1 | hc3⟩) <;> omega
        rw [hfun]
        exact finSum_two_distinct a b (by intro h; have := congrArg Fin.val h; simp [a, b] at this; omega)
      · by_cases hi2 : i.val = 2
        · let a : Fin n := ⟨0, by omega⟩
          let b : Fin n := ⟨2 * M, by omega⟩
          have hfun : (fun j : Fin n => b2n (inFlipSet M j.val i.val)) =
              (fun j : Fin n => if j = a ∨ j = b then 1 else 0) := by
            funext j
            by_cases h : j = a ∨ j = b
            · rcases h with rfl | rfl <;> simp [inFlipSet, hi2, a, b, b2n]
            · have ha : j.val ≠ 0 := fun hv => h (Or.inl (Fin.ext hv))
              have hb : j.val ≠ 2 * M := fun hv => h (Or.inr (Fin.ext hv))
              cases hf : inFlipSet M j.val i.val
              · simp [h, b2n]
              · simp only [inFlipSet, hi2, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
                rcases hf with (((⟨h0, _⟩ | ⟨h2M, _⟩) | ⟨_, h1 | h2M1⟩) | ⟨⟨⟨hge, _⟩, _⟩, hc1 | hc3⟩) <;> omega
          rw [hfun]
          exact finSum_two_distinct a b (by intro h; have := congrArg Fin.val h; simp [a, b] at this; omega)
        · by_cases hi3 : i.val = 3
          · let a : Fin n := ⟨0, by omega⟩
            let b : Fin n := ⟨2 * M, by omega⟩
            have hfun : (fun j : Fin n => b2n (inFlipSet M j.val i.val)) =
                (fun j : Fin n => if j = a ∨ j = b then 1 else 0) := by
              funext j
              by_cases h : j = a ∨ j = b
              · rcases h with rfl | rfl <;> simp [inFlipSet, hi3, a, b, b2n]
              · have ha : j.val ≠ 0 := fun hv => h (Or.inl (Fin.ext hv))
                have hb : j.val ≠ 2 * M := fun hv => h (Or.inr (Fin.ext hv))
                cases hf : inFlipSet M j.val i.val
                · simp [h, b2n]
                · simp only [inFlipSet, hi3, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
                  rcases hf with (((⟨h0, _⟩ | ⟨h2M, _⟩) | ⟨_, h1 | h2M1⟩) | ⟨⟨⟨hge, _⟩, _⟩, hc1 | hc3⟩) <;> omega
            rw [hfun]
            exact finSum_two_distinct a b (by intro h; have := congrArg Fin.val h; simp [a, b] at this; omega)
          · by_cases hi5 : i.val = 5
            · let a : Fin n := ⟨0, by omega⟩
              let b : Fin n := ⟨4, by omega⟩
              have hfun : (fun j : Fin n => b2n (inFlipSet M j.val i.val)) =
                  (fun j : Fin n => if j = a ∨ j = b then 1 else 0) := by
                funext j
                by_cases h : j = a ∨ j = b
                · rcases h with rfl | rfl
                  · simp [inFlipSet, hi5, a, b2n]
                  · have hle4 : 4 ≤ 2 * M - 4 := by omega
                    simp [inFlipSet, hi5, b, hle4, b2n]
                · have ha : j.val ≠ 0 := fun hv => h (Or.inl (Fin.ext hv))
                  have hb : j.val ≠ 4 := fun hv => h (Or.inr (Fin.ext hv))
                  cases hf : inFlipSet M j.val i.val
                  · simp [h, b2n]
                  · simp only [inFlipSet, hi5, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
                    rcases hf with (((⟨h0, _⟩ | ⟨_, h2 | h3⟩) | ⟨_, h1 | h2M1⟩) | ⟨⟨⟨hge, _⟩, _⟩, hc1 | hc3⟩) <;> omega
              rw [hfun]
              exact finSum_two_distinct a b (by intro h; have := congrArg Fin.val h; simp [a, b] at this)
            · -- Odd i with 7 ≤ i ≤ 2M - 1: in-flips come from i - 3 and i - 1!
              have hge7 : 7 ≤ i.val := by omega
              have hle2M1 : i.val ≤ 2 * M - 1 := by omega
              let a : Fin n := ⟨i.val - 3, by omega⟩
              let b : Fin n := ⟨i.val - 1, by omega⟩
              have hfun : (fun j : Fin n => b2n (inFlipSet M j.val i.val)) =
                  (fun j : Fin n => if j = a ∨ j = b then 1 else 0) := by
                funext j
                by_cases h : j = a ∨ j = b
                · rcases h with rfl | rfl
                  · have ha_val : a.val = i.val - 3 := rfl
                    have htrue : inFlipSet M a.val i.val = true := by
                      rw [ha_val]
                      unfold inFlipSet
                      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
                      right
                      exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, Or.inr (by omega)⟩
                    simp [htrue, b2n]
                  · have hb_val : b.val = i.val - 1 := rfl
                    have htrue : inFlipSet M b.val i.val = true := by
                      rw [hb_val]
                      unfold inFlipSet
                      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
                      by_cases hi_top : i.val = 2 * M - 1
                      · left; right; exact ⟨by omega, Or.inr hi_top⟩
                      · right; exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, Or.inl (by omega)⟩
                    simp [htrue, b2n]
                · have ha : j.val ≠ i.val - 3 := fun hv => h (Or.inl (Fin.ext hv))
                  have hb : j.val ≠ i.val - 1 := fun hv => h (Or.inr (Fin.ext hv))
                  cases hf : inFlipSet M j.val i.val
                  · simp [h, b2n]
                  · simp only [inFlipSet, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
                    rcases hf with (((⟨_, ((h1 | h2) | h3) | h5⟩ | ⟨_, h2 | h3⟩) | ⟨h2M2, h1 | h2M1⟩) | ⟨⟨⟨_, _⟩, _⟩, hc1 | hc3⟩) <;> omega
              rw [hfun]
              exact finSum_two_distinct a b (by intro h; have := congrArg Fin.val h; simp [a, b] at this; omega)
    have hout : T.outDeg i = M + 2 := by omega
    rw [hout, isCoprimeOut_iff_gcd_deg]
    exact ⟨by omega, gcd_add_two_double_odd hodd⟩

/-- **Theorem 3.1 (Complete Classification of Complete Graphs `K_n`):**
    For every `n ≥ 1`, the complete graph `K_n` admits a coprime orientation
    if and only if `n % 4 ≠ 1` and `n ≠ 7`. -/
theorem complete_graph_coprime_iff {n : Nat} (hn : n ≥ 1) :
    (∃ T : Tournament n, IsCoprimeTournament T) ↔ n % 4 ≠ 1 ∧ n ≠ 7 := by
  constructor
  · intro hex
    refine ⟨?_, ?_⟩
    · intro hmod
      exact complete_graph_not_coprime_mod4_one hmod hex
    · rintro rfl
      exact complete_graph_not_coprime_seven hex
  · rintro ⟨hmod, hne7⟩
    by_cases heven : n % 2 = 0
    · let k := n / 2
      have hnk : n = 2 * k := by omega
      have hk : k ≥ 1 := by omega
      rw [hnk]
      exact complete_graph_coprime_even hk
    · by_cases h3 : n = 3
      · subst h3; exact complete_graph_coprime_three
      · let M := (n - 1) / 2
        have hnM : n = 2 * M + 1 := by omega
        have hMge5 : M ≥ 5 := by omega
        have hModd : M % 2 = 1 := by omega
        rw [hnM]
        exact complete_graph_coprime_odd_ge_eleven hMge5 hModd

end CoprimeOrientations
