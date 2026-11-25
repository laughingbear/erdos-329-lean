/-
Copyright 2026 Laughing Bear.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# Erdős Problem 329: a Sidon set with upper density at least `1/2`

Proofs of two statements from google-deepmind/formal-conjectures:

* `Erdos329.erdos_329.variants.lower_bound`: there is a Sidon set `A ⊆ ℕ` with
  `limsup |A ∩ [1, N]| / √N ≥ 1/2` (Erdős);
* `Erdos329.exists_sidon_pos_density`: there is a Sidon set with positive such upper density.

The definitions `IsSidon`, `Erdos329.sqrtPartialDensity`, `Erdos329.sidonUpperDensity` and both
statements are copied verbatim from formal-conjectures.

**Construction.** For an odd prime `p`, the Erdős–Turán set
`S_p = {2pk + (k² mod p) : 0 ≤ k < p}` is a Sidon set of `p` elements in `[0, 2p²)` whose
consecutive elements differ by more than `p`. We glue translates `T_j + S_{p_j}` together at
rapidly growing scales: if everything built so far lies below `X`, we take a prime
`p ≥ (j + 1)(X + 1) + 3` and `T = 2p² + X + 1`. The new block lies in `[T, T + 2p²)`, so
sums of two new elements exceed every other sum, and its gaps exceed every difference of old
elements; hence the union stays Sidon (`isSidon_union`). At `N = T + 2p² - 1 ≤ (4 + 1/(j+1)) p²`
the set has at least `p` elements in `[1, N]`, giving `|A ∩ [1, N]| / √N ≥ 1/2 - o(1)`
infinitely often. A Sidon set has `|A ∩ [1, N]| ≤ 3√N` (distinct differences), so the
`limsup` is a genuine one and is at least `1/2`.
-/

section Defs

open Function Set
open scoped Pointwise

variable {α : Type*} [AddCommMonoid α]

/-- A Sidon set is a set, such that such that all pairwise sums of elements are distinct apart from
coincidences forced by the commutativity of addition. -/
def IsSidon (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

end Defs

namespace SidonHalf

/-! ### The Erdős–Turán Sidon set -/

/-- The `k`-th element of the Erdős–Turán set for `p`. -/
def et (p k : ℕ) : ℕ := 2 * p * k + k ^ 2 % p

lemma et_succ (p k : ℕ) (hp : 0 < p) : et p k + p + 1 ≤ et p (k + 1) := by
  unfold et
  have h1 : k ^ 2 % p < p := Nat.mod_lt _ hp
  have h2 : 2 * p * (k + 1) = 2 * p * k + 2 * p := by ring
  omega

lemma et_gap (p : ℕ) (hp : 0 < p) {k k' : ℕ} (h : k < k') : et p k + p + 1 ≤ et p k' := by
  induction k', h using Nat.le_induction with
  | base => exact et_succ p k hp
  | succ n _ ih => have := et_succ p n hp; omega

lemma et_lt (p k : ℕ) (hk : k < p) : et p k < 2 * p ^ 2 := by
  unfold et
  have h1 : k ^ 2 % p < p := Nat.mod_lt _ (by omega)
  have h2 : 2 * p * k + 2 * p ≤ 2 * p ^ 2 := by
    have : 2 * p * (k + 1) ≤ 2 * p * p := Nat.mul_le_mul_left _ hk
    nlinarith
  omega

/-- The Erdős–Turán set is Sidon. -/
lemma et_sidon (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {a b c d : ℕ} (ha : a < p)
    (_hb : b < p) (hc : c < p) (hd : d < p) (h : et p a + et p b = et p c + et p d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hp0 : 0 < p := hp.out.pos
  unfold et at h
  have ra := Nat.mod_lt (a ^ 2) hp0
  have rb := Nat.mod_lt (b ^ 2) hp0
  have rc := Nat.mod_lt (c ^ 2) hp0
  have rd := Nat.mod_lt (d ^ 2) hp0
  have hsum : a + b = c + d := by
    rcases lt_trichotomy (a + b) (c + d) with hlt | heq | hgt
    · have : 2 * p * (a + b + 1) ≤ 2 * p * (c + d) := Nat.mul_le_mul_left _ hlt
      have e1 : 2 * p * (a + b + 1) = 2 * p * a + 2 * p * b + 2 * p := by ring
      have e2 : 2 * p * (c + d) = 2 * p * c + 2 * p * d := by ring
      omega
    · exact heq
    · have : 2 * p * (c + d + 1) ≤ 2 * p * (a + b) := Nat.mul_le_mul_left _ hgt
      have e1 : 2 * p * (c + d + 1) = 2 * p * c + 2 * p * d + 2 * p := by ring
      have e2 : 2 * p * (a + b) = 2 * p * a + 2 * p * b := by ring
      omega
  have hres : a ^ 2 % p + b ^ 2 % p = c ^ 2 % p + d ^ 2 % p := by
    have e1 : 2 * p * (a + b) = 2 * p * a + 2 * p * b := by ring
    have e2 : 2 * p * (c + d) = 2 * p * c + 2 * p * d := by ring
    rw [hsum] at e1
    omega
  have h1 : (a : ZMod p) + b = c + d := by exact_mod_cast congrArg (Nat.cast (R := ZMod p)) hsum
  have h2 : (a : ZMod p) ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by
    have := congrArg (Nat.cast (R := ZMod p)) hres
    push_cast [ZMod.natCast_mod] at this
    exact this
  have two : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this
    exact hp2 this
  have key : (2 : ZMod p) * ((a - c) * (a - d)) = 0 := by
    linear_combination (↑a - ↑b - ↑c - ↑d : ZMod p) * h1 + h2
  rcases mul_eq_zero.1 key with h0 | h0
  · exact absurd h0 two
  have cast_eq : ∀ x y : ℕ, x < p → y < p → (x : ZMod p) = y → x = y := by
    intro x y hx hy hxy
    have := (ZMod.natCast_eq_natCast_iff' x y p).1 hxy
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  rcases mul_eq_zero.1 h0 with h0 | h0
  · have := cast_eq a c ha hc (sub_eq_zero.1 h0)
    left; omega
  · have := cast_eq a d ha hd (sub_eq_zero.1 h0)
    right; omega

/-! ### Blocks -/

/-- The translate `T + S_p` of the Erdős–Turán set. -/
def blk (p T : ℕ) : Set ℕ := {x | ∃ k < p, x = T + et p k}

lemma blk_sidon (p T : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : IsSidon (blk p T) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ h
  have h' : et p a + et p b = et p c + et p d := by omega
  rcases et_sidon p hp2 ha hb hc hd h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; exact ⟨rfl, rfl⟩
  · right; exact ⟨rfl, rfl⟩

lemma blk_bounds {p T x : ℕ} (hx : x ∈ blk p T) : T ≤ x ∧ x < T + 2 * p ^ 2 := by
  obtain ⟨k, hk, rfl⟩ := hx
  have := et_lt p k hk
  omega

lemma blk_gap {p T x y : ℕ} (hp : 0 < p) (hx : x ∈ blk p T) (hy : y ∈ blk p T) (hxy : x < y) :
    x + p + 1 ≤ y := by
  obtain ⟨k, -, rfl⟩ := hx
  obtain ⟨k', -, rfl⟩ := hy
  rcases lt_trichotomy k k' with h | rfl | h
  · have := et_gap p hp h; omega
  · omega
  · have := et_gap p hp h; omega

lemma blk_eq_image (p T : ℕ) :
    blk p T = ((Finset.range p).image (fun k => T + et p k) : Set ℕ) := by
  ext x
  simp only [blk, Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_range, Set.mem_image,
    Set.mem_Iio]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

lemma blk_ncard (p T : ℕ) (hp : 0 < p) : (blk p T).ncard = p := by
  rw [blk_eq_image, Set.ncard_coe_finset, Finset.card_image_of_injective _ ?_,
    Finset.card_range]
  intro k k' h
  simp only at h
  rcases lt_trichotomy k k' with hk | hk | hk
  · have := et_gap p hp hk; omega
  · exact hk
  · have := et_gap p hp hk; omega

/-! ### Gluing two Sidon sets at different scales -/

lemma isSidon_union {A B : Set ℕ} {X T U : ℕ} (hA : IsSidon A) (hB : IsSidon B)
    (hAX : ∀ a ∈ A, a < X) (hBT : ∀ b ∈ B, T ≤ b ∧ b < T + U) (hTU : U + X ≤ T)
    (hTX : 2 * X ≤ T) (hgap : ∀ b ∈ B, ∀ b' ∈ B, b < b' → b + X ≤ b') :
    IsSidon (A ∪ B) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ h
  -- a pair of `B`-elements on opposite sides of the equation must coincide
  have pairB : ∀ b ∈ B, ∀ b' ∈ B, ∀ a ∈ A, ∀ a' ∈ A, b + a = b' + a' → b = b' := by
    intro b hb b' hb' a ha a' ha' he
    have := hAX a ha; have := hAX a' ha'
    rcases lt_trichotomy b b' with hl | hl | hl
    · have := hgap b hb b' hb' hl; omega
    · exact hl
    · have := hgap b' hb' b hb hl; omega
  rcases hi₁ with hi₁ | hi₁ <;> rcases hj₁ with hj₁ | hj₁ <;>
    rcases hi₂ with hi₂ | hi₂ <;> rcases hj₂ with hj₂ | hj₂
  -- all four in `A`
  · exact hA i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ h
  -- exactly one in `B`: one side is `≥ T`, the other `< 2X`
  · have := hAX i₁ hi₁; have := hAX j₁ hj₁; have := hAX i₂ hi₂; have := (hBT j₂ hj₂).1; omega
  · have := hAX i₁ hi₁; have := hAX j₁ hj₁; have := hAX j₂ hj₂; have := (hBT i₂ hi₂).1; omega
  -- `i₂, j₂ ∈ B`
  · have e := pairB i₂ hi₂ j₂ hj₂ i₁ hi₁ j₁ hj₁ (by omega)
    left; omega
  · have := hAX i₁ hi₁; have := hAX i₂ hi₂; have := hAX j₂ hj₂; have := (hBT j₁ hj₁).1; omega
  -- `j₁, j₂ ∈ B`, `i₁, i₂ ∈ A`
  · have := hAX i₁ hi₁; have := hAX i₂ hi₂; have := (hBT j₁ hj₁).1; have := (hBT j₂ hj₂).1
    omega
  -- `i₂, j₁ ∈ B`
  · have e := pairB i₂ hi₂ j₁ hj₁ i₁ hi₁ j₂ hj₂ (by omega)
    right; omega
  -- `j₁, i₂, j₂ ∈ B`, `i₁ ∈ A`
  · have := hAX i₁ hi₁; have := (hBT j₁ hj₁).1; have := (hBT j₂ hj₂).1
    have := (hBT i₂ hi₂).2; omega
  -- only `i₁ ∈ B`
  · have := hAX j₁ hj₁; have := hAX i₂ hi₂; have := hAX j₂ hj₂; have := (hBT i₁ hi₁).1; omega
  -- `i₁, j₂ ∈ B`
  · have e := pairB i₁ hi₁ j₂ hj₂ i₂ hi₂ j₁ hj₁ (by omega)
    right; omega
  -- `i₁, i₂ ∈ B`, `j₁, j₂ ∈ A`
  · have := hAX j₁ hj₁; have := hAX j₂ hj₂; have := (hBT i₁ hi₁).1; have := (hBT i₂ hi₂).1
    omega
  -- `i₁, i₂, j₂ ∈ B`, `j₁ ∈ A`
  · have := hAX j₁ hj₁; have := (hBT i₁ hi₁).1; have := (hBT i₂ hi₂).1
    have := (hBT j₂ hj₂).2; omega
  -- `i₁, j₁ ∈ B`
  · have e := pairB i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ (by omega)
    left; omega
  -- `i₁, j₁, j₂ ∈ B`, `i₂ ∈ A`
  · have := hAX i₂ hi₂; have := (hBT i₁ hi₁).2; have := (hBT j₁ hj₁).1
    have := (hBT j₂ hj₂).1; omega
  -- `i₁, j₁, i₂ ∈ B`, `j₂ ∈ A`
  · have := hAX j₂ hj₂; have := (hBT i₁ hi₁).1; have := (hBT j₁ hj₁).2
    have := (hBT i₂ hi₂).1; omega
  -- all four in `B`
  · exact hB i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ h

/-! ### The construction -/

/-- A prime at least `(j + 1)(X + 1) + 3`. -/
noncomputable def pr (X j : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes ((j + 1) * (X + 1) + 3))

lemma pr_prime (X j : ℕ) : (pr X j).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes ((j + 1) * (X + 1) + 3))).2

lemma pr_ge (X j : ℕ) : (j + 1) * (X + 1) + 3 ≤ pr X j :=
  (Nat.find_spec (Nat.exists_infinite_primes ((j + 1) * (X + 1) + 3))).1

/-- `Xs j` bounds every element of the first `j` blocks. -/
noncomputable def Xs : ℕ → ℕ
  | 0 => 0
  | j + 1 => 4 * pr (Xs j) j ^ 2 + Xs j + 1

/-- The prime used for block `j`. -/
noncomputable def P (j : ℕ) : ℕ := pr (Xs j) j

/-- The offset of block `j`. -/
noncomputable def T (j : ℕ) : ℕ := 2 * P j ^ 2 + Xs j + 1

lemma Xs_succ (j : ℕ) : Xs (j + 1) = T j + 2 * P j ^ 2 := by
  simp only [Xs, T, P]; ring

lemma P_ge (j : ℕ) : (j + 1) * (Xs j + 1) + 3 ≤ P j := pr_ge _ _

lemma P_prime (j : ℕ) : (P j).Prime := pr_prime _ _

lemma P_ne_two (j : ℕ) : P j ≠ 2 := by
  have := P_ge j; intro h; rw [h] at this; nlinarith

lemma P_gt_Xs (j : ℕ) : Xs j + 3 < P j := by
  have := P_ge j; nlinarith

/-- The union of the first `j` blocks. -/
def upto (j : ℕ) : Set ℕ := {x | ∃ i < j, x ∈ blk (P i) (T i)}

/-- The Sidon set. -/
def theSet : Set ℕ := {x | ∃ i, x ∈ blk (P i) (T i)}

lemma upto_succ (j : ℕ) : upto (j + 1) = upto j ∪ blk (P j) (T j) := by
  ext x
  simp only [upto, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact Or.inl ⟨i, hi, hx⟩
    · exact Or.inr hx
  · rintro (⟨i, hi, hx⟩ | hx)
    · exact ⟨i, by omega, hx⟩
    · exact ⟨j, by omega, hx⟩

lemma upto_spec (j : ℕ) : IsSidon (upto j) ∧ ∀ x ∈ upto j, x < Xs j := by
  induction j with
  | zero =>
    refine ⟨?_, ?_⟩
    · rintro _ ⟨i, hi, -⟩; omega
    · rintro _ ⟨i, hi, -⟩; omega
  | succ j ih =>
    obtain ⟨hS, hX⟩ := ih
    have : Fact (P j).Prime := ⟨P_prime j⟩
    have hpX := P_gt_Xs j
    have hp0 : 0 < P j := by omega
    rw [upto_succ]
    refine ⟨isSidon_union hS (blk_sidon _ _ (P_ne_two j)) hX
      (fun b hb => blk_bounds hb) (by simp only [T]; omega) ?_ ?_, ?_⟩
    · have : P j ≤ P j ^ 2 := by nlinarith
      simp only [T]; omega
    · intro b hb b' hb' hbb'
      have := blk_gap hp0 hb hb' hbb'
      omega
    · rintro x (hx | hx)
      · have := hX x hx; rw [Xs_succ]; simp only [T] at *; omega
      · have := blk_bounds hx; rw [Xs_succ]; omega

lemma theSet_sidon : IsSidon theSet := by
  rintro i₁ ⟨a, ha⟩ j₁ ⟨b, hb⟩ i₂ ⟨c, hc⟩ j₂ ⟨d, hd⟩ h
  have hS := (upto_spec (a + b + c + d + 1)).1
  exact hS i₁ ⟨a, by omega, ha⟩ j₁ ⟨b, by omega, hb⟩ i₂ ⟨c, by omega, hc⟩ j₂ ⟨d, by omega, hd⟩ h

/-! ### A Sidon set has at most `3 √N` elements in `[1, N]` -/

lemma card_sq_le (F : Finset ℕ) (N : ℕ) (hF : F ⊆ Finset.Icc 1 N) (hS : IsSidon (F : Set ℕ)) :
    F.card * F.card - F.card ≤ 2 * N + 1 := by
  rw [← Finset.offDiag_card]
  have hmap : Set.MapsTo (fun x : ℕ × ℕ => (x.2 : ℤ) - x.1) (F.offDiag : Set (ℕ × ℕ))
      (Finset.Icc (-(N : ℤ)) N : Set ℤ) := by
    rintro ⟨x, y⟩ hxy
    simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.mem_coe] at hxy
    have hx := Finset.mem_Icc.1 (hF hxy.1)
    have hy := Finset.mem_Icc.1 (hF hxy.2.1)
    simp only [Finset.coe_Icc, Set.mem_Icc]
    omega
  have hinj : Set.InjOn (fun x : ℕ × ℕ => (x.2 : ℤ) - x.1) (F.offDiag : Set (ℕ × ℕ)) := by
    rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' he
    simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.mem_coe] at hxy hxy'
    simp only at he
    have he' : y + x' = y' + x := by omega
    rcases hS y hxy.2.1 y' hxy'.2.1 x' hxy'.1 x hxy.1 he' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · exact absurd h1.symm hxy.2.2
  have := Finset.card_le_card_of_injOn _ hmap hinj
  simp only [Int.card_Icc] at this
  omega

lemma ratio_le (A : Set ℕ) (hA : IsSidon A) (N : ℕ) :
    ((A ∩ Set.Icc 1 N).ncard : ℝ) / (N : ℝ).sqrt ≤ 3 := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set F : Finset ℕ := (Finset.Icc 1 N).filter (· ∈ A)
  have hFS : IsSidon (F : Set ℕ) := by
    intro a ha b hb c hc d hd h
    simp only [F, Finset.coe_filter, Set.mem_ofPred_eq] at ha hb hc hd
    exact hA a ha.2 b hb.2 c hc.2 d hd.2 h
  have hset : (A ∩ Set.Icc 1 N).ncard = F.card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext y
    simp only [F, Finset.coe_filter, Finset.mem_Icc, Set.mem_inter_iff, Set.mem_Icc,
      Set.mem_ofPred_eq]; tauto
  have hc := card_sq_le F N (Finset.filter_subset _ _) hFS
  rw [hset]
  set k := F.card
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set s := (N : ℝ).sqrt with hs
  have hs2 : s ^ 2 = N := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.2 hN1
  have hk : (k : ℝ) * k ≤ 2 * N + 1 + k := by
    have : k * k ≤ 2 * N + 1 + k := by omega
    exact_mod_cast this
  rw [div_le_iff₀ (by linarith)]
  by_contra hcon
  push Not at hcon
  have hk0 : (0 : ℝ) ≤ k := by positivity
  nlinarith

/-! ### Infinitely many good `N` -/

lemma good_N (j : ℕ) :
    let N := Xs (j + 1) - 1
    j ≤ N ∧ (P j : ℝ) ≤ ((theSet ∩ Set.Icc 1 N).ncard : ℝ) ∧
      ((j + 1 : ℕ) : ℝ) * N ≤ (4 * (j + 1) + 1 : ℕ) * (P j : ℝ) ^ 2 := by
  intro N
  have hpX := P_gt_Xs j
  have hpg := P_ge j
  have hN : N = T j + 2 * P j ^ 2 - 1 := by simp only [N, Xs_succ]
  have hT : T j = 2 * P j ^ 2 + Xs j + 1 := rfl
  have hp0 : 0 < P j := by omega
  have hpp : P j ≤ P j ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have : j + 1 ≤ P j := by nlinarith
    omega
  · have hsub : blk (P j) (T j) ⊆ theSet ∩ Set.Icc 1 N := by
      intro x hx
      refine ⟨⟨j, hx⟩, ?_⟩
      have := blk_bounds hx
      simp only [Set.mem_Icc]; omega
    have hfin : (theSet ∩ Set.Icc 1 N).Finite := (Set.finite_Icc 1 N).subset Set.inter_subset_right
    have := Set.ncard_le_ncard hsub hfin
    rw [blk_ncard _ _ hp0] at this
    exact_mod_cast this
  · have key : (j + 1) * N ≤ (4 * (j + 1) + 1) * P j ^ 2 := by
      have h1 : (j + 1) * (Xs j + 1) ≤ P j ^ 2 := by omega
      have h2 : N ≤ 4 * P j ^ 2 + Xs j := by omega
      calc (j + 1) * N ≤ (j + 1) * (4 * P j ^ 2 + Xs j) := Nat.mul_le_mul_left _ h2
        _ ≤ (4 * (j + 1) + 1) * P j ^ 2 := by nlinarith
    exact_mod_cast key

lemma frequently_ge (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ N : ℕ in Filter.atTop,
      1 / 2 - ε ≤ ((theSet ∩ Set.Icc 1 N).ncard : ℝ) / (N : ℝ).sqrt := by
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨j, hj⟩ : ∃ j : ℕ, a ≤ j ∧ 1 / ε ≤ j := ⟨a + ⌈1 / ε⌉₊, by omega,
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_add_left _ _)⟩
  obtain ⟨hjN, hcnt, hbound⟩ := good_N j
  set N := Xs (j + 1) - 1
  refine ⟨N, hj.1.trans hjN, ?_⟩
  set p : ℝ := (P j : ℝ)
  have hp : (1 : ℝ) ≤ p := by
    have := P_gt_Xs j; simp only [p]; exact_mod_cast (show 1 ≤ P j by omega)
  set δ : ℝ := 1 / ((j : ℝ) + 1) with hδ
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδε : δ ≤ ε := by
    rw [hδ, div_le_iff₀ hj1]
    have := hj.2
    rw [div_le_iff₀ hε] at this
    nlinarith
  have hNle : (N : ℝ) ≤ (p * (2 + δ / 4)) ^ 2 := by
    have hb : ((j : ℝ) + 1) * N ≤ (4 * ((j : ℝ) + 1) + 1) * p ^ 2 := by
      push_cast at hbound; exact hbound
    have : (N : ℝ) ≤ (4 + δ) * p ^ 2 := by
      rw [hδ, show (4 + 1 / ((j : ℝ) + 1)) * p ^ 2 =
        (4 * ((j : ℝ) + 1) + 1) * p ^ 2 / ((j : ℝ) + 1) by field_simp, le_div_iff₀ hj1]
      linarith
    nlinarith [sq_nonneg (δ * p)]
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := by
      have := P_gt_Xs j
      have : 1 ≤ P j ^ 2 := Nat.one_le_pow _ _ (by omega)
      simp only [N, Xs_succ, T]; omega
    exact_mod_cast this
  have hsq : (N : ℝ).sqrt ≤ p * (2 + δ / 4) := by
    rw [Real.sqrt_le_left (by positivity)]
    exact hNle
  have hsqpos : 0 < (N : ℝ).sqrt := Real.sqrt_pos.2 hNpos
  rw [le_div_iff₀ hsqpos]
  calc (1 / 2 - ε) * (N : ℝ).sqrt ≤ (1 / 2 - δ / 16) * (p * (2 + δ / 4)) := by
        rcases le_or_gt (1 / 2 - ε) 0 with h | h
        · have : (1 / 2 - ε) * (N : ℝ).sqrt ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hsqpos.le
          have : 0 ≤ (1 / 2 - δ / 16) * (p * (2 + δ / 4)) := by
            apply mul_nonneg _ (by positivity)
            have : δ ≤ 1 := by
              rw [hδ, div_le_one hj1]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
            linarith
          linarith
        · calc (1 / 2 - ε) * (N : ℝ).sqrt ≤ (1 / 2 - ε) * (p * (2 + δ / 4)) :=
                mul_le_mul_of_nonneg_left hsq h.le
            _ ≤ (1 / 2 - δ / 16) * (p * (2 + δ / 4)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
    _ ≤ p := by nlinarith [sq_nonneg δ]
    _ ≤ _ := hcnt

end SidonHalf

open Function Set Filter

namespace Erdos329

/--
The partial density of a Sidon set `A` up to `N`, normalized by dividing by `√N` instead of `N`.
This measures how close the set comes to the optimal density for Sidon sets.
-/
noncomputable def sqrtPartialDensity (A : Set ℕ) (N : ℕ) : ℝ :=
  (A ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt

/-- The upper density of a Sidon set `A`, normalized by `√N`. -/
noncomputable def sidonUpperDensity (A : Set ℕ) : ℝ :=
  limsup (fun N => sqrtPartialDensity A N) atTop

theorem erdos_329.variants.lower_bound : ∃ (A : Set ℕ), IsSidon A ∧ sidonUpperDensity A ≥ 1/2 := by
  refine ⟨SidonHalf.theSet, SidonHalf.theSet_sidon, ?_⟩
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun N => sqrtPartialDensity SidonHalf.theSet N) :=
    isBoundedUnder_of ⟨3, fun N => SidonHalf.ratio_le _ SidonHalf.theSet_sidon N⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := le_limsup_of_frequently_le (SidonHalf.frequently_ge ε hε) hbdd
  unfold sidonUpperDensity
  unfold sqrtPartialDensity at *
  linarith

theorem exists_sidon_pos_density : ∃ (A : Set ℕ), IsSidon A ∧ 0 < sidonUpperDensity A := by
  obtain ⟨A, hA, h⟩ := erdos_329.variants.lower_bound
  exact ⟨A, hA, by linarith⟩

end Erdos329
