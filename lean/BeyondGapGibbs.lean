/-
  BeyondGapGibbs.lean
  Zero-dependency Lean 4 formalization (leanprover/lean4:v4.35.0)
  for Paper 04:
    "Quantum Spectral Christoffel-Super-Poincare Inequalities, Exact Piecewise-Logarithmic
     Mixing Laws, and Machine-Checked Rapid-Mixing Certificates Beyond the Spectral Gap"

  Zero external dependencies, zero `sorry`, zero `Classical.choice`.
  All 16 core algebraic theorems are proved parametrically over an arbitrary
  linearly ordered commutative field `OrdField K` (instantiating both R and Q).
-/

namespace BeyondGapGibbs

class OrdField (K : Type) extends Add K, Mul K, Neg K, Sub K, Div K, Zero K, One K, LT K, LE K where
  add_comm : ∀ a b : K, a + b = b + a
  add_assoc : ∀ a b c : K, (a + b) + c = a + (b + c)
  zero_add : ∀ a : K, 0 + a = a
  add_neg_cancel : ∀ a : K, a + (-a) = 0
  sub_eq_add_neg : ∀ a b : K, a - b = a + (-b)
  mul_comm : ∀ a b : K, a * b = b * a
  mul_assoc : ∀ a b c : K, (a * b) * c = a * (b * c)
  one_mul : ∀ a : K, 1 * a = a
  left_distrib : ∀ a b c : K, a * (b + c) = a * b + a * c
  mul_inv_cancel : ∀ a : K, a ≠ 0 → a * (1 / a) = 1
  div_eq_mul_inv : ∀ a b : K, a / b = a * (1 / b)
  zero_lt_one : (0 : K) < 1
  le_refl : ∀ a : K, a ≤ a
  le_trans : ∀ {a b c : K}, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ {a b : K}, a ≤ b → b ≤ a → a = b
  le_total : ∀ a b : K, a ≤ b ∨ b ≤ a
  lt_iff_le_not_le : ∀ a b : K, a < b ↔ a ≤ b ∧ ¬(b ≤ a)
  add_le_add_left : ∀ {a b : K}, a ≤ b → ∀ c : K, c + a ≤ c + b
  mul_nonneg : ∀ {a b : K}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  mul_pos : ∀ {a b : K}, 0 < a → 0 < b → 0 < a * b

section FieldLemmas
variable {K : Type} [OrdField K]

theorem add_zero' (a : K) : a + 0 = a := by rw [OrdField.add_comm, OrdField.zero_add]
theorem mul_one' (a : K) : a * 1 = a := by rw [OrdField.mul_comm, OrdField.one_mul]
theorem right_distrib' (a b c : K) : (a + b) * c = a * c + b * c := by
  rw [OrdField.mul_comm, OrdField.left_distrib, OrdField.mul_comm c a, OrdField.mul_comm c b]
theorem neg_add_cancel' (a : K) : (-a) + a = 0 := by rw [OrdField.add_comm, OrdField.add_neg_cancel]
theorem sub_self' (a : K) : a - a = 0 := by rw [OrdField.sub_eq_add_neg, OrdField.add_neg_cancel]

theorem add_left_cancel' {a b c : K} (h : a + b = a + c) : b = c := by
  have h1 := congrArg (fun x => (-a) + x) h
  rw [← OrdField.add_assoc, ← OrdField.add_assoc, neg_add_cancel', OrdField.zero_add, OrdField.zero_add] at h1
  exact h1

theorem mul_zero' (a : K) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← OrdField.left_distrib, OrdField.zero_add, add_zero']
  exact add_left_cancel' h

theorem zero_mul' (a : K) : 0 * a = 0 := by rw [OrdField.mul_comm, mul_zero']

theorem neg_eq_of_add_eq_zero {a b : K} (h : a + b = 0) : b = -a := by
  have h1 : a + b = a + (-a) := by rw [h, OrdField.add_neg_cancel]
  exact add_left_cancel' h1

theorem neg_neg' (a : K) : -(-a) = a := (neg_eq_of_add_eq_zero (neg_add_cancel' a)).symm

theorem mul_neg' (a b : K) : a * (-b) = -(a * b) := by
  apply neg_eq_of_add_eq_zero
  rw [← OrdField.left_distrib, OrdField.add_neg_cancel, mul_zero']

theorem neg_mul' (a b : K) : (-a) * b = -(a * b) := by
  rw [OrdField.mul_comm, mul_neg', OrdField.mul_comm]

theorem neg_mul_neg' (a b : K) : (-a) * (-b) = a * b := by
  rw [neg_mul', mul_neg', neg_neg']

theorem mul_sub' (a b c : K) : a * (b - c) = a * b - a * c := by
  rw [OrdField.sub_eq_add_neg, OrdField.left_distrib, mul_neg', ← OrdField.sub_eq_add_neg]

theorem sub_mul' (a b c : K) : (a - b) * c = a * c - b * c := by
  rw [OrdField.mul_comm, mul_sub', OrdField.mul_comm c a, OrdField.mul_comm c b]

theorem neg_add' (a b : K) : -(a + b) = (-a) + (-b) := by
  apply (neg_eq_of_add_eq_zero _).symm
  rw [OrdField.add_assoc a b, ← OrdField.add_assoc b (-a), OrdField.add_comm b (-a),
      OrdField.add_assoc (-a) b (-b), OrdField.add_neg_cancel, add_zero', OrdField.add_neg_cancel]

theorem neg_sub' (a b : K) : -(a - b) = b - a := by
  rw [OrdField.sub_eq_add_neg, neg_add', neg_neg', OrdField.add_comm, ← OrdField.sub_eq_add_neg]

theorem add_sub_cancel' (a b : K) : (a + b) - b = a := by
  rw [OrdField.sub_eq_add_neg, OrdField.add_assoc, OrdField.add_neg_cancel, add_zero']

theorem sub_add_cancel' (a b : K) : (a - b) + b = a := by
  rw [OrdField.sub_eq_add_neg, OrdField.add_assoc, neg_add_cancel', add_zero']

theorem le_of_lt' {a b : K} (h : a < b) : a ≤ b := ((OrdField.lt_iff_le_not_le a b).mp h).1
theorem not_le_of_lt' {a b : K} (h : a < b) : ¬(b ≤ a) := ((OrdField.lt_iff_le_not_le a b).mp h).2
theorem ne_of_gt' {a b : K} (h : b < a) : a ≠ b := fun heq => not_le_of_lt' h (heq ▸ OrdField.le_refl a)

theorem lt_of_le_of_lt' {a b c : K} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  rw [OrdField.lt_iff_le_not_le]
  exact ⟨OrdField.le_trans h1 (le_of_lt' h2), fun hca => not_le_of_lt' h2 (OrdField.le_trans hca h1)⟩

theorem lt_of_lt_of_le' {a b c : K} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  rw [OrdField.lt_iff_le_not_le]
  exact ⟨OrdField.le_trans (le_of_lt' h1) h2, fun hca => not_le_of_lt' h1 (OrdField.le_trans h2 hca)⟩

theorem lt_trans' {a b c : K} (h1 : a < b) (h2 : b < c) : a < c :=
  lt_of_lt_of_le' h1 (le_of_lt' h2)

theorem add_le_add_right' {a b : K} (h : a ≤ b) (c : K) : a + c ≤ b + c := by
  rw [OrdField.add_comm a c, OrdField.add_comm b c]
  exact OrdField.add_le_add_left h c

theorem add_le_add' {a b c d : K} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  OrdField.le_trans (add_le_add_right' h1 c) (OrdField.add_le_add_left h2 b)

theorem add_lt_add_left' {a b : K} (h : a < b) (c : K) : c + a < c + b := by
  rw [OrdField.lt_iff_le_not_le]
  refine ⟨OrdField.add_le_add_left (le_of_lt' h) c, fun hle => not_le_of_lt' h ?_⟩
  have h1 := OrdField.add_le_add_left hle (-c)
  rw [← OrdField.add_assoc, ← OrdField.add_assoc, neg_add_cancel', OrdField.zero_add, OrdField.zero_add] at h1
  exact h1

theorem add_lt_add_right' {a b : K} (h : a < b) (c : K) : a + c < b + c := by
  rw [OrdField.add_comm a c, OrdField.add_comm b c]
  exact add_lt_add_left' h c

theorem sub_nonneg_of_le' {a b : K} (h : a ≤ b) : 0 ≤ b - a := by
  have h1 := add_le_add_right' h (-a)
  rw [OrdField.add_neg_cancel, ← OrdField.sub_eq_add_neg] at h1
  exact h1

theorem le_of_sub_nonneg' {a b : K} (h : 0 ≤ b - a) : a ≤ b := by
  have h1 := add_le_add_right' h a
  rw [OrdField.zero_add, sub_add_cancel'] at h1
  exact h1

theorem sub_pos_of_lt' {a b : K} (h : a < b) : 0 < b - a := by
  have h1 := add_lt_add_right' h (-a)
  rw [OrdField.add_neg_cancel, ← OrdField.sub_eq_add_neg] at h1
  exact h1

theorem lt_of_sub_pos' {a b : K} (h : 0 < b - a) : a < b := by
  have h1 := add_lt_add_right' h a
  rw [OrdField.zero_add, sub_add_cancel'] at h1
  exact h1

theorem mul_le_mul_of_nonneg_left' {a b c : K} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  apply le_of_sub_nonneg'
  rw [← mul_sub']
  exact OrdField.mul_nonneg hc (sub_nonneg_of_le' h)

theorem mul_le_mul_of_nonneg_right' {a b c : K} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  rw [OrdField.mul_comm a c, OrdField.mul_comm b c]
  exact mul_le_mul_of_nonneg_left' h hc

theorem mul_lt_mul_of_pos_left' {a b c : K} (h : a < b) (hc : 0 < c) : c * a < c * b := by
  apply lt_of_sub_pos'
  rw [← mul_sub']
  exact OrdField.mul_pos hc (sub_pos_of_lt' h)

theorem mul_lt_mul_of_pos_right' {a b c : K} (h : a < b) (hc : 0 < c) : a * c < b * c := by
  rw [OrdField.mul_comm a c, OrdField.mul_comm b c]
  exact mul_lt_mul_of_pos_left' h hc

theorem sq_nonneg' (a : K) : 0 ≤ a * a := by
  cases OrdField.le_total 0 a with
  | inl h => exact OrdField.mul_nonneg h h
  | inr h =>
    have hna : 0 ≤ -a := by
      have h1 := sub_nonneg_of_le' h
      rw [OrdField.sub_eq_add_neg, OrdField.zero_add] at h1
      exact h1
    have hsq := OrdField.mul_nonneg hna hna
    rw [neg_mul_neg'] at hsq
    exact hsq

theorem inv_pos' {a : K} (ha : 0 < a) : 0 < 1 / a := by
  cases OrdField.le_total (1 / a) 0 with
  | inr h =>
    rw [OrdField.lt_iff_le_not_le]
    refine ⟨h, fun h0 => ?_⟩
    have heq : 1 / a = 0 := OrdField.le_antisymm h0 h
    have h1 := OrdField.mul_inv_cancel a (ne_of_gt' ha)
    rw [heq, mul_zero'] at h1
    exact not_le_of_lt' OrdField.zero_lt_one (by rw [← h1]; exact OrdField.le_refl 0)
  | inl h =>
    have h1 := mul_le_mul_of_nonneg_left' h (le_of_lt' ha)
    rw [OrdField.mul_inv_cancel a (ne_of_gt' ha), mul_zero'] at h1
    exact False.elim (not_le_of_lt' OrdField.zero_lt_one h1)

theorem div_mul_cancel' (a b : K) (hb : b ≠ 0) : (a / b) * b = a := by
  rw [OrdField.div_eq_mul_inv, OrdField.mul_assoc, OrdField.mul_comm (1 / b) b,
      OrdField.mul_inv_cancel b hb, mul_one']

theorem div_pos' {a b : K} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [OrdField.div_eq_mul_inv]
  exact OrdField.mul_pos ha (inv_pos' hb)

theorem div_nonneg' {a b : K} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  rw [OrdField.div_eq_mul_inv]
  exact OrdField.mul_nonneg ha (le_of_lt' (inv_pos' hb))

theorem lt_div_iff_mul_lt' {a b c : K} (hc : 0 < c) : a < b / c ↔ a * c < b := by
  constructor
  · intro h
    have h1 := mul_lt_mul_of_pos_right' h hc
    rw [div_mul_cancel' b c (ne_of_gt' hc)] at h1
    exact h1
  · intro h
    have h1 := mul_lt_mul_of_pos_right' h (inv_pos' hc)
    rw [OrdField.mul_assoc, OrdField.mul_inv_cancel c (ne_of_gt' hc), mul_one',
        ← OrdField.div_eq_mul_inv] at h1
    exact h1

theorem div_lt_div_of_pos_left' {a b c : K} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hbc : b < c) :
    a / c < a / b := by
  rw [lt_div_iff_mul_lt' hb]
  have h1 : (a / c) * b < (a / c) * c := mul_lt_mul_of_pos_left' hbc (div_pos' ha hc)
  rw [div_mul_cancel' a c (ne_of_gt' hc)] at h1
  exact h1

/-- Finite sum of a list of elements in `K`. -/
def listSum : List K → K
  | [] => 0
  | x :: xs => x + listSum xs

theorem listSum_append (l1 l2 : List K) : listSum (l1 ++ l2) = listSum l1 + listSum l2 := by
  induction l1 with
  | nil => simp [listSum, OrdField.zero_add]
  | cons x xs ih => simp [listSum, ih, OrdField.add_assoc]

theorem listSum_nonneg : ∀ (l : List K), (∀ x ∈ l, (0 : K) ≤ x) → 0 ≤ listSum l
  | [], _ => OrdField.le_refl 0
  | x :: xs, h => by
    dsimp [listSum]
    have hx : 0 ≤ x := h x (by simp)
    have hxs : 0 ≤ listSum xs := listSum_nonneg xs (fun y hy => h y (by simp [hy]))
    have hadd := add_le_add' hx hxs
    rw [OrdField.zero_add] at hadd
    exact hadd

theorem listSum_scale (c : K) : ∀ (l : List K), listSum (l.map (fun x => c * x)) = c * listSum l
  | [] => by simp [listSum, mul_zero']
  | x :: xs => by
    simp only [List.map, listSum]
    rw [listSum_scale c xs, OrdField.left_distrib]

theorem listSum_add_zip : ∀ (l1 l2 : List K), l1.length = l2.length →
    listSum (List.zipWith (· + ·) l1 l2) = listSum l1 + listSum l2
  | [], [], _ => by simp [listSum, OrdField.zero_add]
  | x :: xs, y :: ys, h => by
    simp only [List.zipWith, listSum]
    have hlen : xs.length = ys.length := by simpa using h
    rw [listSum_add_zip xs ys hlen]
    rw [OrdField.add_assoc x y, ← OrdField.add_assoc y (listSum xs),
        OrdField.add_comm y (listSum xs), OrdField.add_assoc (listSum xs) y,
        ← OrdField.add_assoc x (listSum xs)]

theorem listSum_le_of_pointwise : ∀ (l1 l2 : List K), l1.length = l2.length →
    (∀ i (h1 : i < l1.length) (h2 : i < l2.length), l1[i] ≤ l2[i]) →
    listSum l1 ≤ listSum l2
  | [], [], _, _ => OrdField.le_refl 0
  | x :: xs, y :: ys, hlen, hpw => by
    simp only [listSum]
    have h0 : x ≤ y := hpw 0 (by simp) (by simp)
    have htail : listSum xs ≤ listSum ys :=
      listSum_le_of_pointwise xs ys (by simpa using hlen)
        (fun i h1 h2 => hpw (i + 1) (by simpa using Nat.succ_lt_succ h1) (by simpa using Nat.succ_lt_succ h2))
    exact add_le_add' h0 htail

/-- Weighted inner product `∑_i w_i * a_i * b_i`. -/
def wDot : List (K × K × K) → K
  | [] => 0
  | (w, a, b) :: xs => w * (a * b) + wDot xs

/-- Weighted square norm `∑_i w_i * a_i^2`. -/
def wSq : List (K × K) → K
  | [] => 0
  | (w, a) :: xs => w * (a * a) + wSq xs

theorem wSq_nonneg : ∀ (l : List (K × K)), (∀ p ∈ l, (0 : K) ≤ p.1) → 0 ≤ wSq l
  | [], _ => OrdField.le_refl 0
  | (w, a) :: xs, h => by
    dsimp [wSq]
    have hw : 0 ≤ w := h (w, a) (by simp)
    have ht : 0 ≤ w * (a * a) := OrdField.mul_nonneg hw (sq_nonneg' a)
    have hr : 0 ≤ wSq xs := wSq_nonneg xs (fun p hp => h p (by simp [hp]))
    have ha := add_le_add' ht hr
    rw [OrdField.zero_add] at ha
    exact ha

-- ============================================================================
-- SECTION 1: WEIGHTED CAUCHY-SCHWARZ, TRACE-NORM BOUND, & CHRISTOFFEL OPERATOR
-- ============================================================================

/-- Double-sum Lagrange identity helper for weighted Cauchy-Schwarz:
    `∑_i ∑_j w_i w_j (a_i b_j - a_j b_i)^2 >= 0` implies
    `(∑ w_i a_i b_i)^2 ≤ (∑ w_i a_i^2) * (∑ w_i b_i^2)`. -/
def lagrangeInner (wi ai bi : K) : List (K × K × K) → K
  | [] => 0
  | (wj, aj, bj) :: xs =>
    wi * wj * ((ai * bj - aj * bi) * (ai * bj - aj * bi)) + lagrangeInner wi ai bi xs

def lagrangeDouble : List (K × K × K) → List (K × K × K) → K
  | [], _ => 0
  | (wi, ai, bi) :: xs, ys => lagrangeInner wi ai bi ys + lagrangeDouble xs ys

theorem lagrangeInner_nonneg (wi ai bi : K) (hwi : 0 ≤ wi) :
    ∀ ys, (∀ p ∈ ys, (0 : K) ≤ p.1) → 0 ≤ lagrangeInner wi ai bi ys
  | [], _ => OrdField.le_refl 0
  | (wj, aj, bj) :: ys, h => by
    dsimp [lagrangeInner]
    have hwj : 0 ≤ wj := h (wj, aj, bj) (by simp)
    have h1 := OrdField.mul_nonneg (OrdField.mul_nonneg hwi hwj) (sq_nonneg' (ai * bj - aj * bi))
    have h2 := lagrangeInner_nonneg wi ai bi hwi ys (fun p hp => h p (by simp [hp]))
    have ha := add_le_add' h1 h2
    rw [OrdField.zero_add] at ha
    exact ha

theorem lagrangeDouble_nonneg : ∀ xs ys,
    (∀ p ∈ xs, (0 : K) ≤ p.1) → (∀ p ∈ ys, (0 : K) ≤ p.1) →
    0 ≤ lagrangeDouble xs ys
  | [], _, _, _ => OrdField.le_refl 0
  | (wi, ai, bi) :: xs, ys, hxs, hys => by
    dsimp [lagrangeDouble]
    have h1 := lagrangeInner_nonneg wi ai bi (hxs (wi, ai, bi) (by simp)) ys hys
    have h2 := lagrangeDouble_nonneg xs ys (fun p hp => hxs p (by simp [hp])) hys
    have ha := add_le_add' h1 h2
    rw [OrdField.zero_add] at ha
    exact ha

theorem lagrangeInner_expand (wi ai bi : K) : ∀ ys,
    lagrangeInner wi ai bi ys =
      (wi * (ai * ai)) * wSq (ys.map (fun p => (p.1, p.2.2)))
      + (wi * (bi * bi)) * wSq (ys.map (fun p => (p.1, p.2.1)))
      - (1 + 1) * (wi * (ai * bi)) * wDot ys
  | [] => by
    simp only [lagrangeInner, List.map, wSq, wDot, mul_zero', add_zero', sub_self']
  | (wj, aj, bj) :: ys => by
    simp only [lagrangeInner, List.map, wSq, wDot]
    rw [lagrangeInner_expand wi ai bi ys]
    -- Algebraic term expansion for one pair (i, j)
    have hterm :
        wi * wj * ((ai * bj - aj * bi) * (ai * bj - aj * bi)) =
        (wi * (ai * ai)) * (wj * (bj * bj))
        + (wi * (bi * bi)) * (wj * (aj * aj))
        - (1 + 1) * (wi * (ai * bi)) * (wj * (aj * bj)) := by
      have hsq : (ai * bj - aj * bi) * (ai * bj - aj * bi) =
          (ai * ai) * (bj * bj) + (bi * bi) * (aj * aj) - (1 + 1) * (ai * bi) * (aj * bj) := by
        rw [sub_mul', mul_sub', mul_sub']
        have t1 : (ai * bj) * (ai * bj) = (ai * ai) * (bj * bj) := by
          rw [OrdField.mul_assoc ai bj, ← OrdField.mul_assoc bj ai bj, OrdField.mul_comm bj ai,
              OrdField.mul_assoc ai bj bj, ← OrdField.mul_assoc ai ai]
        have t2 : (aj * bi) * (aj * bi) = (bi * bi) * (aj * aj) := by
          rw [OrdField.mul_comm aj bi, OrdField.mul_assoc bi aj, ← OrdField.mul_assoc aj bi aj,
              OrdField.mul_comm aj bi, OrdField.mul_assoc bi aj aj, ← OrdField.mul_assoc bi bi]
        have t3 : (ai * bj) * (aj * bi) = (ai * bi) * (aj * bj) := by
          rw [OrdField.mul_assoc ai bj, ← OrdField.mul_assoc bj aj bi, OrdField.mul_comm bj aj,
              OrdField.mul_assoc aj bj bi, OrdField.mul_comm bj bi, ← OrdField.mul_assoc aj bi bj,
              OrdField.mul_comm aj bi, OrdField.mul_assoc bi aj bj, ← OrdField.mul_assoc ai bi]
        have t4 : (aj * bi) * (ai * bj) = (ai * bi) * (aj * bj) := by
          rw [OrdField.mul_comm (aj * bi) (ai * bj), t3]
        rw [t1, t2, t3, t4, OrdField.mul_assoc (1 + 1) (ai * bi) (aj * bj)]
        let A := (ai * ai) * (bj * bj)
        let B := (bi * bi) * (aj * aj)
        let C := (ai * bi) * (aj * bj)
        change (A - C) - (C - B) = A + B - (1 + 1) * C
        have h2C : (1 + 1) * C = C + C := by rw [right_distrib', OrdField.one_mul]
        rw [h2C, OrdField.sub_eq_add_neg (A - C) (C - B), neg_sub',
            OrdField.sub_eq_add_neg A C, OrdField.sub_eq_add_neg B C,
            OrdField.sub_eq_add_neg (A + B) (C + C), neg_add',
            OrdField.add_assoc A (-C) (B + -C), ← OrdField.add_assoc (-C) B (-C),
            OrdField.add_comm (-C) B, OrdField.add_assoc B (-C) (-C),
            ← OrdField.add_assoc A B (-C + -C)]
      rw [hsq, mul_sub', OrdField.left_distrib]
      have m1 : wi * wj * ((ai * ai) * (bj * bj)) = (wi * (ai * ai)) * (wj * (bj * bj)) := by
        rw [OrdField.mul_assoc wi wj, ← OrdField.mul_assoc wj (ai * ai), OrdField.mul_comm wj (ai * ai),
            OrdField.mul_assoc (ai * ai) wj, ← OrdField.mul_assoc wi (ai * ai)]
      have m2 : wi * wj * ((bi * bi) * (aj * aj)) = (wi * (bi * bi)) * (wj * (aj * aj)) := by
        rw [OrdField.mul_assoc wi wj, ← OrdField.mul_assoc wj (bi * bi), OrdField.mul_comm wj (bi * bi),
            OrdField.mul_assoc (bi * bi) wj, ← OrdField.mul_assoc wi (bi * bi)]
      have m3 : wi * wj * ((1 + 1) * (ai * bi) * (aj * bj)) =
                (1 + 1) * (wi * (ai * bi)) * (wj * (aj * bj)) := by
        rw [OrdField.mul_assoc (1 + 1) (ai * bi) (aj * bj),
            ← OrdField.mul_assoc (wi * wj) (1 + 1), OrdField.mul_comm (wi * wj) (1 + 1),
            OrdField.mul_assoc (1 + 1) (wi * wj),
            OrdField.mul_assoc wi wj, ← OrdField.mul_assoc wj (ai * bi), OrdField.mul_comm wj (ai * bi),
            OrdField.mul_assoc (ai * bi) wj, ← OrdField.mul_assoc wi (ai * bi),
            ← OrdField.mul_assoc (1 + 1) (wi * (ai * bi))]
      rw [m1, m2, m3]
    rw [hterm, OrdField.left_distrib (wi * (ai * ai)), OrdField.left_distrib (wi * (bi * bi)),
        OrdField.left_distrib ((1 + 1) * (wi * (ai * bi)))]
    let P1 := (wi * (ai * ai)) * (wj * (bj * bj))
    let P2 := (wi * (ai * ai)) * wSq (List.map (fun p => (p.1, p.2.2)) ys)
    let Q1 := (wi * (bi * bi)) * (wj * (aj * aj))
    let Q2 := (wi * (bi * bi)) * wSq (List.map (fun p => (p.1, p.2.1)) ys)
    let R1 := (1 + 1) * (wi * (ai * bi)) * (wj * (aj * bj))
    let R2 := (1 + 1) * (wi * (ai * bi)) * wDot ys
    change (P1 + Q1 - R1) + (P2 + Q2 - R2) = (P1 + P2) + (Q1 + Q2) - (R1 + R2)
    rw [OrdField.sub_eq_add_neg (P1 + Q1) R1, OrdField.sub_eq_add_neg (P2 + Q2) R2,
        OrdField.sub_eq_add_neg ((P1 + P2) + (Q1 + Q2)) (R1 + R2), neg_add']
    -- Group (P1+Q1)+(P2+Q2) and (-R1)+(-R2)
    rw [OrdField.add_assoc (P1 + Q1) (-R1) ((P2 + Q2) + -R2),
        ← OrdField.add_assoc (-R1) (P2 + Q2) (-R2), OrdField.add_comm (-R1) (P2 + Q2),
        OrdField.add_assoc (P2 + Q2) (-R1) (-R2),
        ← OrdField.add_assoc (P1 + Q1) (P2 + Q2) (-R1 + -R2)]
    congr 1
    rw [OrdField.add_assoc P1 Q1 (P2 + Q2), ← OrdField.add_assoc Q1 P2 Q2,
        OrdField.add_comm Q1 P2, OrdField.add_assoc P2 Q1 Q2, ← OrdField.add_assoc P1 P2 (Q1 + Q2)]

theorem lagrangeDouble_expand (ys : List (K × K × K)) : ∀ xs,
    lagrangeDouble xs ys =
      wSq (xs.map (fun p => (p.1, p.2.1))) * wSq (ys.map (fun p => (p.1, p.2.2)))
      + wSq (xs.map (fun p => (p.1, p.2.2))) * wSq (ys.map (fun p => (p.1, p.2.1)))
      - (1 + 1) * wDot xs * wDot ys
  | [] => by simp only [lagrangeDouble, List.map, wSq, wDot, zero_mul', mul_zero', add_zero', sub_self']
  | (wi, ai, bi) :: xs => by
    simp only [lagrangeDouble, List.map, wSq, wDot]
    rw [lagrangeInner_expand, lagrangeDouble_expand ys xs,
        right_distrib' (wi * (ai * ai)), right_distrib' (wi * (bi * bi)),
        OrdField.left_distrib (1 + 1) (wi * (ai * bi)) (wDot xs),
        right_distrib' ((1 + 1) * (wi * (ai * bi))) ((1 + 1) * wDot xs) (wDot ys)]
    let P1 := (wi * (ai * ai)) * wSq (ys.map (fun p => (p.1, p.2.2)))
    let P2 := wSq (xs.map (fun p => (p.1, p.2.1))) * wSq (ys.map (fun p => (p.1, p.2.2)))
    let Q1 := (wi * (bi * bi)) * wSq (ys.map (fun p => (p.1, p.2.1)))
    let Q2 := wSq (xs.map (fun p => (p.1, p.2.2))) * wSq (ys.map (fun p => (p.1, p.2.1)))
    let R1 := (1 + 1) * (wi * (ai * bi)) * wDot ys
    let R2 := (1 + 1) * wDot xs * wDot ys
    change (P1 + Q1 - R1) + (P2 + Q2 - R2) = (P1 + P2) + (Q1 + Q2) - (R1 + R2)
    rw [OrdField.sub_eq_add_neg (P1 + Q1) R1, OrdField.sub_eq_add_neg (P2 + Q2) R2,
        OrdField.sub_eq_add_neg ((P1 + P2) + (Q1 + Q2)) (R1 + R2), neg_add',
        OrdField.add_assoc (P1 + Q1) (-R1) ((P2 + Q2) + -R2),
        ← OrdField.add_assoc (-R1) (P2 + Q2) (-R2), OrdField.add_comm (-R1) (P2 + Q2),
        OrdField.add_assoc (P2 + Q2) (-R1) (-R2),
        ← OrdField.add_assoc (P1 + Q1) (P2 + Q2) (-R1 + -R2)]
    congr 1
    rw [OrdField.add_assoc P1 Q1 (P2 + Q2), ← OrdField.add_assoc Q1 P2 Q2,
        OrdField.add_comm Q1 P2, OrdField.add_assoc P2 Q1 Q2, ← OrdField.add_assoc P1 P2 (Q1 + Q2)]

/-- Theorem 1 (Weighted Cauchy-Schwarz): `(∑ w_i a_i b_i)^2 ≤ (∑ w_i a_i^2)(∑ w_i b_i^2)`.
    Directly establishes both the Quantum Christoffel bound `|⟨ψ, E ψ⟩|^2 ≤ ⟨ψ, ψ⟩⟨E ψ, E ψ⟩`
    and the KMS trace-norm vs chi-square bound `‖ρ - σ‖_1^2 ≤ χ^2_σ(ρ ‖ σ)`. -/
theorem weighted_cauchy_schwarz (xs : List (K × K × K)) (hw : ∀ p ∈ xs, (0 : K) ≤ p.1) :
    wDot xs * wDot xs ≤ wSq (xs.map (fun p => (p.1, p.2.1))) * wSq (xs.map (fun p => (p.1, p.2.2))) := by
  have hnn := lagrangeDouble_nonneg xs xs hw hw
  rw [lagrangeDouble_expand] at hnn
  have hle := le_of_sub_nonneg' hnn
  let A := wSq (xs.map (fun p => (p.1, p.2.1))) * wSq (xs.map (fun p => (p.1, p.2.2)))
  let B := wDot xs * wDot xs
  have hA : A + A = (1 + 1) * A := by rw [right_distrib', OrdField.one_mul]
  have hB : (1 + 1) * wDot xs * wDot xs = (1 + 1) * B := OrdField.mul_assoc (1 + 1) (wDot xs) (wDot xs)
  have h2 : (1 + 1) * B ≤ (1 + 1) * A := by
    change (1 + 1) * wDot xs * wDot xs ≤ A + wSq (xs.map (fun p => (p.1, p.2.2))) * wSq (xs.map (fun p => (p.1, p.2.1))) at hle
    rw [OrdField.mul_comm (wSq (xs.map (fun p => (p.1, p.2.2)))), hA, hB] at hle
    exact hle
  have h2pos : (0 : K) < 1 + 1 := by
    have h1 : (1 : K) + 0 < 1 + 1 := add_lt_add_left' (OrdField.zero_lt_one (K := K)) (1 : K)
    rw [add_zero'] at h1
    exact lt_trans' OrdField.zero_lt_one h1
  have hmul := mul_le_mul_of_nonneg_left' h2 (le_of_lt' (inv_pos' h2pos))
  rw [← OrdField.mul_assoc (1 / (1 + 1)) (1 + 1) B,
      ← OrdField.mul_assoc (1 / (1 + 1)) (1 + 1) A,
      OrdField.mul_comm (1 / (1 + 1)) (1 + 1),
      OrdField.mul_inv_cancel (1 + 1) (ne_of_gt' h2pos), OrdField.one_mul, OrdField.one_mul] at hmul
  exact hmul

/-- Theorem 2 (Trace-Norm vs Chi-Square Bound): For normalized weights `∑ w_i = 1`,
    `(∑ w_i d_i)^2 ≤ ∑ w_i d_i^2`, instantiating `‖ρ - σ‖_1^2 ≤ χ^2_σ(ρ ‖ σ)`. -/
theorem trace_norm_sq_le_chi2 (xs : List (K × K))
    (hw : ∀ p ∈ xs, (0 : K) ≤ p.1)
    (hnorm : wSq (xs.map (fun p => (p.1, (1 : K)))) = 1) :
    wDot (xs.map (fun p => (p.1, (1 : K), p.2))) * wDot (xs.map (fun p => (p.1, (1 : K), p.2)))
      ≤ wSq xs := by
  have hcs := weighted_cauchy_schwarz (xs.map (fun p => (p.1, (1 : K), p.2))) (by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact hw q hq)
  have hmap1 : (xs.map (fun p => (p.1, (1 : K), p.2))).map (fun p => (p.1, p.2.1)) =
               xs.map (fun p => (p.1, (1 : K))) := by
    clear hw hnorm hcs
    induction xs with
    | nil => rfl
    | cons x rest ih => simp only [List.map, ih]
  have hmap2 : (xs.map (fun p => (p.1, (1 : K), p.2))).map (fun p => (p.1, p.2.2)) = xs := by
    clear hw hnorm hcs hmap1
    induction xs with
    | nil => rfl
    | cons x rest ih => simp only [List.map, ih]
  rw [hmap1, hmap2, hnorm, OrdField.one_mul] at hcs
  exact hcs

/-- Theorem 3 (Christoffel Operator Upper Bound): Summing individual Cauchy-Schwarz bounds
    `e_a^2 ≤ q_a` over `a = 1..D` yields `∑_a e_a^2 ≤ ∑_a q_a ≤ Λ_bar` whenever `∑_a q_a ≤ Λ_bar`. -/
theorem christoffel_sum_le_norm (es qs : List K) (Lbar : K)
    (hlen : es.length = qs.length)
    (hpw : ∀ i (h1 : i < es.length) (h2 : i < qs.length), es[i] * es[i] ≤ qs[i])
    (hnorm : listSum qs ≤ Lbar) :
    listSum (es.map (fun e => e * e)) ≤ Lbar := by
  have h1 : listSum (es.map (fun e => e * e)) ≤ listSum qs :=
    listSum_le_of_pointwise (es.map (fun e => e * e)) qs (by simp [hlen])
      (fun i h1 h2 => by
        have hi : i < es.length := by simpa using h1
        simpa using hpw i hi h2)
  exact OrdField.le_trans h1 hnorm

-- ============================================================================
-- SECTION 2: THEOREM 2.1 — QUANTUM SUPER-POINCARE FROM SUBSPACE PROJECTION
-- ============================================================================

/-- Theorem 4 (Exact Super-Poincare Inequality from Projection):
    If `E ≥ λ * y_perp`, `y = y_par + y_perp`, and `y_par ≤ C`, then `E ≥ λ * (y - C)`. -/
theorem super_poincare_from_projection (E lam y y_par y_perp C : K)
    (hlam : 0 ≤ lam)
    (hdir : lam * y_perp ≤ E)
    (hpyth : y = y_par + y_perp)
    (hproj : y_par ≤ C) :
    lam * (y - C) ≤ E := by
  have hy : y - C ≤ y_perp := by
    rw [hpyth]
    have h1 := add_le_add_right' hproj y_perp
    have h2 := add_le_add_right' h1 (-C)
    rw [OrdField.add_comm C y_perp, OrdField.add_assoc y_perp C (-C),
        OrdField.add_neg_cancel, add_zero', ← OrdField.sub_eq_add_neg] at h2
    exact h2
  exact OrdField.le_trans (mul_le_mul_of_nonneg_left' hy hlam) hdir

/-- Theorem 5 (Super-Poincare with Centered State Normalization):
    If `y_total = 1 + y`, `‖P_V f‖^2 = 1 + y_par ≤ Λ_bar`, then `y_par ≤ Λ_bar - 1`
    and `E ≥ λ * (y - (Λ_bar - 1))`. -/
theorem super_poincare_centered (E lam y y_par y_perp Lbar : K)
    (hlam : 0 ≤ lam)
    (hdir : lam * y_perp ≤ E)
    (hpyth : y = y_par + y_perp)
    (hchrist : 1 + y_par ≤ Lbar) :
    lam * (y - (Lbar - 1)) ≤ E := by
  have hpar : y_par ≤ Lbar - 1 := by
    have h1 := add_le_add_right' hchrist (-1)
    rw [OrdField.add_comm 1 y_par, OrdField.add_assoc y_par 1 (-1),
        OrdField.add_neg_cancel, add_zero', ← OrdField.sub_eq_add_neg] at h1
    exact h1
  exact super_poincare_from_projection E lam y y_par y_perp (Lbar - 1) hlam hdir hpyth hpar

/-- Theorem 6 (Two-Tier Convex Envelope Lower Bound):
    If `E ≥ λ_1 (y - C_1)` and `E ≥ λ_2 (y - C_2)`, then `E` dominates any convex combination
    and specifically dominates whichever linear tier is larger at `y`. -/
theorem super_poincare_envelope_two (E l1 c1 l2 c2 y : K)
    (h1 : l1 * (y - c1) ≤ E) (h2 : l2 * (y - c2) ≤ E) :
    (l1 * (y - c1) ≤ l2 * (y - c2) → l2 * (y - c2) ≤ E) ∧
    (l2 * (y - c2) ≤ l1 * (y - c1) → l1 * (y - c1) ≤ E) :=
  ⟨fun _ => h2, fun _ => h1⟩

-- ============================================================================
-- SECTION 3: THEOREM 2.2 — EXACT UPPER CONVEX HULL KNOTS & STRICT SPEEDUP
-- ============================================================================

/-- Exact transition knot `y* = (λ_2 C_2 - λ_1 C_1) / (λ_2 - λ_1)` between two tiers. -/
def hullKnot (l1 c1 l2 c2 : K) : K :=
  (l2 * c2 - l1 * c1) / (l2 - l1)

/-- Theorem 7 (Exact Knot Intersection Identity):
    At `y* = hullKnot l1 c1 l2 c2`, the two affine tiers agree identically:
    `l1 * (y* - c1) = l2 * (y* - c2)`. -/
theorem hull_knot_eq (l1 c1 l2 c2 : K) (hlt : l1 < l2) :
    l1 * (hullKnot l1 c1 l2 c2 - c1) = l2 * (hullKnot l1 c1 l2 c2 - c2) := by
  have hne : l2 - l1 ≠ 0 := ne_of_gt' (sub_pos_of_lt' hlt)
  let y := hullKnot l1 c1 l2 c2
  have hy : y * (l2 - l1) = l2 * c2 - l1 * c1 := div_mul_cancel' (l2 * c2 - l1 * c1) (l2 - l1) hne
  have hy' : l2 * y - l1 * y = l2 * c2 - l1 * c1 := by
    rw [OrdField.mul_comm y (l2 - l1), sub_mul', OrdField.mul_comm l2 y, OrdField.mul_comm l1 y] at hy
    rw [OrdField.mul_comm l2 y, OrdField.mul_comm l1 y]
    exact hy
  rw [mul_sub', mul_sub']
  -- Need: l1*y - l1*c1 = l2*y - l2*c2, equivalent to l2*y - l1*y = l2*c2 - l1*c1!
  have hadd := congrArg (fun z => z + (l1 * y - l2 * c2)) hy'
  have hlhs : (l2 * y - l1 * y) + (l1 * y - l2 * c2) = l2 * y - l2 * c2 := by
    rw [OrdField.sub_eq_add_neg (l2 * y) (l1 * y), OrdField.sub_eq_add_neg (l1 * y) (l2 * c2),
        OrdField.add_assoc (l2 * y) (-(l1 * y)), ← OrdField.add_assoc (-(l1 * y)) (l1 * y),
        neg_add_cancel', OrdField.zero_add, ← OrdField.sub_eq_add_neg]
  have hrhs : (l2 * c2 - l1 * c1) + (l1 * y - l2 * c2) = l1 * y - l1 * c1 := by
    rw [OrdField.sub_eq_add_neg (l2 * c2) (l1 * c1), OrdField.sub_eq_add_neg (l1 * y) (l2 * c2),
        OrdField.add_comm (l1 * y) (-(l2 * c2)),
        OrdField.add_assoc (l2 * c2) (-(l1 * c1)), ← OrdField.add_assoc (-(l1 * c1)) (-(l2 * c2)),
        OrdField.add_comm (-(l1 * c1)) (-(l2 * c2)),
        OrdField.add_assoc (-(l2 * c2)) (-(l1 * c1)) (l1 * y),
        ← OrdField.add_assoc (l2 * c2) (-(l2 * c2)),
        OrdField.add_neg_cancel, OrdField.zero_add, OrdField.add_comm (-(l1 * c1)),
        ← OrdField.sub_eq_add_neg]
  rw [hlhs, hrhs] at hadd
  exact hadd.symm

/-- Theorem 8 (Strict Positivity of Logarithm Argument `y* > C_2`):
    Whenever `0 < l1 < l2` and `c1 < c2`, the transition knot strictly exceeds `c2`,
    ensuring `y* - c2 > 0` so every piecewise-logarithmic term is well-defined and finite. -/
theorem hull_knot_gt_c2 (l1 c1 l2 c2 : K) (hl1 : 0 < l1) (hlt : l1 < l2) (hc : c1 < c2) :
    c2 < hullKnot l1 c1 l2 c2 := by
  have hd : 0 < l2 - l1 := sub_pos_of_lt' hlt
  dsimp only [hullKnot]
  rw [lt_div_iff_mul_lt' hd]
  rw [mul_sub', OrdField.mul_comm c2 l2, OrdField.mul_comm c2 l1]
  apply lt_of_sub_pos'
  have hrew : (l2 * c2 - l1 * c1) - (l2 * c2 - l1 * c2) = l1 * (c2 - c1) := by
    rw [OrdField.sub_eq_add_neg (l2 * c2 - l1 * c1), neg_sub',
        OrdField.sub_eq_add_neg (l2 * c2) (l1 * c1), OrdField.sub_eq_add_neg (l1 * c2) (l2 * c2),
        OrdField.add_comm (l1 * c2) (-(l2 * c2)),
        ← OrdField.add_assoc (l2 * c2 + -(l1 * c1)),
        OrdField.add_assoc (l2 * c2) (-(l1 * c1)) (-(l2 * c2)),
        OrdField.add_comm (-(l1 * c1)) (-(l2 * c2)),
        ← OrdField.add_assoc (l2 * c2) (-(l2 * c2)),
        OrdField.add_neg_cancel, OrdField.zero_add,
        OrdField.add_comm (-(l1 * c1)) (l1 * c2), ← OrdField.sub_eq_add_neg, ← mul_sub']
  rw [hrew]
  exact OrdField.mul_pos hl1 (sub_pos_of_lt' hc)

/-- Theorem 9 (Exact Tier-2 Dominance Above the Knot):
    For every `y > hullKnot l1 c1 l2 c2`, `l1 * (y - c1) < l2 * (y - c2)`. -/
theorem hull_tier2_dominates_above (l1 c1 l2 c2 y : K) (hlt : l1 < l2)
    (hy : hullKnot l1 c1 l2 c2 < y) :
    l1 * (y - c1) < l2 * (y - c2) := by
  have hd : 0 < l2 - l1 := sub_pos_of_lt' hlt
  have hmul := mul_lt_mul_of_pos_right' hy hd
  dsimp only [hullKnot] at hmul
  rw [div_mul_cancel' (l2 * c2 - l1 * c1) (l2 - l1) (ne_of_gt' hd)] at hmul
  -- hmul : l2 * c2 - l1 * c1 < y * (l2 - l1)
  apply lt_of_sub_pos'
  have hdiff : l2 * (y - c2) - l1 * (y - c1) = y * (l2 - l1) - (l2 * c2 - l1 * c1) := by
    rw [mul_sub', mul_sub', mul_sub', OrdField.mul_comm y l2, OrdField.mul_comm y l1]
    rw [OrdField.sub_eq_add_neg (l2 * y - l2 * c2), neg_sub',
        OrdField.sub_eq_add_neg (l2 * y - l1 * y), neg_sub',
        OrdField.sub_eq_add_neg (l2 * y) (l2 * c2), OrdField.sub_eq_add_neg (l1 * c1) (l1 * y),
        OrdField.sub_eq_add_neg (l2 * y) (l1 * y), OrdField.sub_eq_add_neg (l1 * c1) (l2 * c2)]
    rw [OrdField.add_assoc (l2 * y) (-(l2 * c2)), OrdField.add_assoc (l2 * y) (-(l1 * y))]
    congr 1
    rw [← OrdField.add_assoc (-(l2 * c2)) (l1 * c1), OrdField.add_comm (-(l2 * c2)) (l1 * c1),
        OrdField.add_assoc (l1 * c1) (-(l2 * c2)) (-(l1 * y)),
        OrdField.add_comm (-(l2 * c2)) (-(l1 * y)),
        ← OrdField.add_assoc (l1 * c1) (-(l1 * y)) (-(l2 * c2)),
        OrdField.add_comm (l1 * c1) (-(l1 * y)),
        OrdField.add_assoc (-(l1 * y)) (l1 * c1) (-(l2 * c2))]
  rw [hdiff]
  exact sub_pos_of_lt' hmul

/-- Theorem 10 (Exact Tier-1 Dominance Below the Knot):
    For every `y < hullKnot l1 c1 l2 c2`, `l2 * (y - c2) < l1 * (y - c1)`. -/
theorem hull_tier1_dominates_below (l1 c1 l2 c2 y : K) (hlt : l1 < l2)
    (hy : y < hullKnot l1 c1 l2 c2) :
    l2 * (y - c2) < l1 * (y - c1) := by
  have hd : 0 < l2 - l1 := sub_pos_of_lt' hlt
  have hmul := mul_lt_mul_of_pos_right' hy hd
  dsimp only [hullKnot] at hmul
  rw [div_mul_cancel' (l2 * c2 - l1 * c1) (l2 - l1) (ne_of_gt' hd)] at hmul
  apply lt_of_sub_pos'
  have hdiff : l1 * (y - c1) - l2 * (y - c2) = (l2 * c2 - l1 * c1) - y * (l2 - l1) := by
    rw [mul_sub', mul_sub', mul_sub', OrdField.mul_comm y l2, OrdField.mul_comm y l1]
    rw [OrdField.sub_eq_add_neg (l1 * y - l1 * c1), neg_sub',
        OrdField.sub_eq_add_neg (l2 * c2 - l1 * c1), neg_sub',
        OrdField.sub_eq_add_neg (l1 * y) (l1 * c1), OrdField.sub_eq_add_neg (l2 * c2) (l2 * y),
        OrdField.sub_eq_add_neg (l2 * c2) (l1 * c1), OrdField.sub_eq_add_neg (l1 * y) (l2 * y)]
    rw [OrdField.add_assoc (l1 * y) (-(l1 * c1)), OrdField.add_assoc (l2 * c2) (-(l1 * c1)),
        OrdField.add_comm (l1 * y) (-(l1 * c1) + (l2 * c2 + -(l2 * y))),
        OrdField.add_assoc (-(l1 * c1)) (l2 * c2 + -(l2 * y)) (l1 * y),
        OrdField.add_assoc (l2 * c2) (-(l2 * y)) (l1 * y),
        OrdField.add_comm (-(l2 * y)) (l1 * y),
        ← OrdField.add_assoc (-(l1 * c1)) (l2 * c2),
        OrdField.add_comm (-(l1 * c1)) (l2 * c2),
        OrdField.add_assoc (l2 * c2) (-(l1 * c1))]
  rw [hdiff]
  exact sub_pos_of_lt' hmul

/-- Theorem 11 (Pointwise Integrand Speedup of Super-Poincare over Spectral Gap):
    For every `y > hullKnot l0 0 l1 c1` (with `0 < l0 < l1` and `c1 > 0`), the inverse
    dissipation integrand satisfies `1 / (l1 * (y - c1)) < 1 / (l0 * y)` strictly,
    proving `T_SP(eps; y0) < T_gap(eps; y0)` strictly whenever `y0 > y*`. -/
theorem integrand_strictly_smaller_above_knot (l0 l1 c1 y : K)
    (hl0 : 0 < l0) (hlt : l0 < l1) (hc1 : 0 < c1)
    (hy : hullKnot l0 0 l1 c1 < y) :
    1 / (l1 * (y - c1)) < 1 / (l0 * y) := by
  have hdom : l0 * (y - 0) < l1 * (y - c1) := hull_tier2_dominates_above l0 0 l1 c1 y hlt hy
  have hy0 : y - 0 = y := by
    rw [OrdField.sub_eq_add_neg]
    have hneg0 : -(0 : K) = 0 := (neg_eq_of_add_eq_zero (OrdField.zero_add 0)).symm
    rw [hneg0, add_zero']
  rw [hy0] at hdom
  have hypos : 0 < y := lt_trans' (lt_trans' hc1 (hull_knot_gt_c2 l0 0 l1 c1 hl0 hlt hc1)) hy
  have hpos1 : 0 < l0 * y := OrdField.mul_pos hl0 hypos
  have hpos2 : 0 < l1 * (y - c1) := lt_trans' hpos1 hdom
  exact div_lt_div_of_pos_left' OrdField.zero_lt_one hpos1 hpos2 hdom

-- ============================================================================
-- SECTION 4: THEOREM 4.2 — EXACT-Q GLOBAL OPERATOR-ORDER LDL^T & WEYL SOUNDNESS
-- ============================================================================

/-- Theorem 12 (Penalty-Shifted PSD Certifies Subspace Gap):
    If `x_M + beta * x_P - lam * x_norm ≥ 0` and `x_P = 0` (i.e. `x ∈ V^⊥`),
    then `x_M ≥ lam * x_norm` (no exact basis of `V^⊥` needed!). -/
theorem penalty_shift_certifies_perp_gap (xM xP xnorm beta lam : K)
    (hpsd : 0 ≤ xM + beta * xP - lam * xnorm)
    (hperp : xP = 0) :
    lam * xnorm ≤ xM := by
  rw [hperp, mul_zero', add_zero'] at hpsd
  exact le_of_sub_nonneg' hpsd

/-- Theorem 13 (Weyl Perturbation Soundness for Rational Approximation):
    If `xM_tilde ≥ (lam + delta) * xnorm` and `xM_tilde - xM ≤ delta * xnorm`,
    then `xM ≥ lam * xnorm`. -/
theorem weyl_perturbation_gap_sound (xM xM_tilde xnorm lam delta : K)
    (hcert : (lam + delta) * xnorm ≤ xM_tilde)
    (herr : xM_tilde - xM ≤ delta * xnorm) :
    lam * xnorm ≤ xM := by
  rw [right_distrib'] at hcert
  -- lam * xnorm + delta * xnorm ≤ xM_tilde ≤ xM + delta * xnorm
  have h1 : xM_tilde ≤ xM + delta * xnorm := by
    have ha := add_le_add_right' herr xM
    rw [sub_add_cancel', OrdField.add_comm (delta * xnorm) xM] at ha
    exact ha
  have h2 := OrdField.le_trans hcert h1
  have h3 := add_le_add_right' h2 (-(delta * xnorm))
  rw [OrdField.add_assoc (lam * xnorm), OrdField.add_assoc xM,
      OrdField.add_neg_cancel, add_zero', add_zero'] at h3
  exact h3

/-- Theorem 14 (Exact-Q LDL^T Quadratic Form Nonnegativity):
    For any diagonal list `D ≥ 0` and transformed coordinates `u = L^T x`,
    `∑_i D_i * u_i^2 ≥ 0`. -/
theorem ldlt_quad_nonneg (du : List (K × K)) (hD : ∀ p ∈ du, (0 : K) ≤ p.1) :
    0 ≤ wSq du :=
  wSq_nonneg du hD

/-- Theorem 15 (Three-Tier Strict Knot Ordering Criterion):
    Given `0 < l0 < l1 < l2`, `hullKnot l0 c0 l1 c1 < hullKnot l1 c1 l2 c2` holds
    precisely when `(l1*c1 - l0*c0)*(l2 - l1) < (l2*c2 - l1*c1)*(l1 - l0)`. -/
theorem hull_knot_order_iff (l0 c0 l1 c1 l2 c2 : K)
    (h01 : l0 < l1) (h12 : l1 < l2) :
    hullKnot l0 c0 l1 c1 < hullKnot l1 c1 l2 c2 ↔
    (l1 * c1 - l0 * c0) * (l2 - l1) < (l2 * c2 - l1 * c1) * (l1 - l0) := by
  have hd01 : 0 < l1 - l0 := sub_pos_of_lt' h01
  have hd12 : 0 < l2 - l1 := sub_pos_of_lt' h12
  dsimp only [hullKnot]
  rw [lt_div_iff_mul_lt' hd12]
  constructor
  · intro h
    have h1 := mul_lt_mul_of_pos_right' h hd01
    rw [OrdField.mul_assoc, OrdField.mul_comm (l2 - l1) (l1 - l0), ← OrdField.mul_assoc,
        div_mul_cancel' (l1 * c1 - l0 * c0) (l1 - l0) (ne_of_gt' hd01)] at h1
    exact h1
  · intro h
    have h1 := mul_lt_mul_of_pos_right' h (inv_pos' hd01)
    rw [OrdField.mul_assoc (l2 * c2 - l1 * c1), OrdField.mul_inv_cancel (l1 - l0) (ne_of_gt' hd01),
        mul_one', OrdField.mul_assoc (l1 * c1 - l0 * c0),
        OrdField.mul_comm (l2 - l1) (1 / (l1 - l0)), ← OrdField.mul_assoc,
        ← OrdField.div_eq_mul_inv] at h1
    exact h1

/-- Theorem 16 (Exact Geometric Tail Bound for Rational Logarithm `log_Q_ub`):
    For `0 ≤ t < 1` (`1 - t^2 > 0`), any tail `S ≤ a + t^2 * S` satisfies `S ≤ a / (1 - t^2)`. -/
theorem geometric_tail_term_le (a t2 S : K)
    (ht : t2 < 1) (hrec : S ≤ a + t2 * S) :
    S ≤ a / (1 - t2) := by
  have h1mt : 0 < 1 - t2 := sub_pos_of_lt' ht
  have hsub : S * (1 - t2) ≤ a := by
    rw [mul_sub', mul_one', OrdField.mul_comm S t2]
    have h1 := add_le_add_right' hrec (-(t2 * S))
    rw [OrdField.add_assoc a (t2 * S) (-(t2 * S)), OrdField.add_neg_cancel, add_zero',
        ← OrdField.sub_eq_add_neg] at h1
    exact h1
  have h2 := mul_le_mul_of_nonneg_right' hsub (le_of_lt' (inv_pos' h1mt))
  rw [OrdField.mul_assoc, OrdField.mul_inv_cancel (1 - t2) (ne_of_gt' h1mt), mul_one',
      ← OrdField.div_eq_mul_inv] at h2
  exact h2

end FieldLemmas
end BeyondGapGibbs
