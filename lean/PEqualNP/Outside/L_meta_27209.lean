import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27209

open PEqualNP.CircuitLowerBounds

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def evalW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl stepW w

theorem eval_eq_evalW (C : Circuit) (x : List Bool) :
    C.eval x = (evalW C.gates x).getD C.output false := rfl

theorem getD_append_right_single (w : List Bool) (b : Bool) (k : ℕ) :
    (w ++ [b]).getD k false = if k < w.length then w.getD k false else if k = w.length then b else false := by
  by_cases h1 : k < w.length
  · simp [h1, List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : k = w.length
    · subst h2
      simp [List.getD_eq_getElem?_getD]
    · simp only [h2, ↓reduceIte]
      have h3 : (w ++ [b]).length ≤ k := by simp; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h3]

theorem evalW_agree_except (gs : List Gate) (u : ℕ) :
    ∀ (w1 w2 : List Bool),
      w1.length = w2.length →
      (∀ k, k ≠ u → w1.getD k false = w2.getD k false) →
      (∀ g ∈ gs, u ∉ g.inputs) →
      (evalW gs w1).length = (evalW gs w2).length ∧
      (∀ k, k ≠ u → (evalW gs w1).getD k false = (evalW gs w2).getD k false) := by
  induction gs with
  | nil =>
    intro w1 w2 hlen hagr _
    exact ⟨hlen, hagr⟩
  | cons g rest ih =>
    intro w1 w2 hlen hagr hno
    have hg : u ∉ g.inputs := hno g (List.mem_cons_self ..)
    have hmap : g.inputs.map (fun i => w1.getD i false) = g.inputs.map (fun i => w2.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagr i (fun heq => hg (heq ▸ hi))
    have hstep_len : (stepW w1 g).length = (stepW w2 g).length := by
      simp [stepW, hlen]
    have hstep_agr : ∀ k, k ≠ u → (stepW w1 g).getD k false = (stepW w2 g).getD k false := by
      intro k hk
      simp only [stepW, getD_append_right_single, hlen, hmap]
      by_cases h1 : k < w2.length
      · simp only [h1, ↓reduceIte]
        exact hagr k hk
      · simp only [h1, ↓reduceIte]
    exact ih (stepW w1 g) (stepW w2 g) hstep_len hstep_agr (fun g' hg' => hno g' (List.mem_cons_of_mem g hg'))

theorem list_length_eq_sum_count (l : List ℕ) (m : ℕ) (h : ∀ x ∈ l, x < m) :
    l.length = ∑ w ∈ Finset.range m, l.count w := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a < m := h a (List.mem_cons_self ..)
    have ht : ∀ x ∈ t, x < m := fun x hx => h x (List.mem_cons_of_mem a hx)
    simp only [List.length_cons, List.count_cons, beq_iff_eq]
    rw [Finset.sum_add_distrib, ← ih ht]
    have h1 : (∑ w ∈ Finset.range m, if a = w then 1 else 0) = 1 := by
      simp [Finset.mem_range.mpr ha]
    omega

theorem flatMap_len_le (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap (fun g => g.inputs)).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g t ih =>
    have hg := h g (List.mem_cons_self ..)
    have ht := ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem ofFn_getD_eq (x : Fin 9 → Bool) (k : ℕ) :
    (List.ofFn x).getD k false = if hk : k < 9 then x ⟨k, hk⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases hk : k < 9
  · simp [hk]
  · simp [hk]

def mkX (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Fin 9 → Bool
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨5, _⟩ => b5
  | ⟨6, _⟩ => b6
  | ⟨7, _⟩ => b7
  | ⟨8, _⟩ => b8

theorem pm3_depends_on (i : Fin 9) :
    ∃ x1 x2 : Fin 9 → Bool, (∀ k : Fin 9, k ≠ i → x1 k = x2 k) ∧ pm3 x1 ≠ pm3 x2 := by
  fin_cases i
  · exact ⟨mkX false false false false true false false false true,
           mkX true false false false true false false false true, by decide, by decide⟩
  · exact ⟨mkX false false false true false false false false true,
           mkX false true false true false false false false true, by decide, by decide⟩
  · exact ⟨mkX false false false false true false true false false,
           mkX false false true false true false true false false, by decide, by decide⟩
  · exact ⟨mkX false true false false false false false false true,
           mkX false true false true false false false false true, by decide, by decide⟩
  · exact ⟨mkX true false false false false false false false true,
           mkX true false false false true false false false true, by decide, by decide⟩
  · exact ⟨mkX true false false false false false false true false,
           mkX true false false false false true false true false, by decide, by decide⟩
  · exact ⟨mkX false false true false true false false false false,
           mkX false false true false true false true false false, by decide, by decide⟩
  · exact ⟨mkX true false false false false true false false false,
           mkX true false false false false true false true false, by decide, by decide⟩
  · exact ⟨mkX true false false false true false false false false,
           mkX true false false false true false false false true, by decide, by decide⟩

theorem in_rest_of_agree (g0 g1 : Gate) (rest : List Gate) (C : Circuit)
    (hgs : C.gates = g0 :: g1 :: rest)
    (heval : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x)
    (w : ℕ) (hw : C.output ≠ w)
    (x1 x2 : Fin 9 → Bool)
    (h2 : ∀ k : Fin 11, k.val ≠ w →
      (stepW (stepW (List.ofFn x1) g0) g1).getD k.val false =
      (stepW (stepW (List.ofFn x2) g0) g1).getD k.val false)
    (hpm : pm3 x1 ≠ pm3 x2) :
    ∃ g ∈ rest, w ∈ g.inputs := by
  by_contra hno
  have hno' : ∀ g ∈ rest, w ∉ g.inputs := fun g hg hmem => hno ⟨g, hg, hmem⟩
  let w2_1 := stepW (stepW (List.ofFn x1) g0) g1
  let w2_2 := stepW (stepW (List.ofFn x2) g0) g1
  have hlen1 : w2_1.length = 11 := by simp [w2_1, stepW]
  have hlen2 : w2_2.length = 11 := by simp [w2_2, stepW]
  have hagr : ∀ k, k ≠ w → w2_1.getD k false = w2_2.getD k false := by
    intro k hk
    by_cases hk11 : k < 11
    · exact h2 ⟨k, hk11⟩ hk
    · have hge1 : w2_1.length ≤ k := by omega
      have hge2 : w2_2.length ≤ k := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]
  have hres := evalW_agree_except rest w w2_1 w2_2 (by omega) hagr hno'
  have hce : C.eval (List.ofFn x1) = C.eval (List.ofFn x2) := by
    rw [eval_eq_evalW, eval_eq_evalW, hgs]
    exact hres.2 C.output hw
  rw [heval x1, heval x2] at hce
  exact hpm hce

theorem no_circuit_disjoint_bin (u1 v1 u2 v2 : ℕ) (op0 op1 : GateOp)
    (hu1v1 : u1 ≠ v1) (hu1u2 : u1 ≠ u2) (hu1v2 : u1 ≠ v2)
    (hv1u2 : v1 ≠ u2) (hv1v2 : v1 ≠ v2) (hu2v2 : u2 ≠ v2)
    (hu19 : u1 < 9) (hv19 : v1 < 9) (hu29 : u2 < 9) (hv29 : v2 < 9)
    (xA1 xA2 xB1 xB2 xC1 xC2 xD1 xD2 : Fin 9 → Bool)
    (hA2 : ∀ k : Fin 11, k.val ≠ u1 →
      (stepW (stepW (List.ofFn xA1) ⟨op0, [u1, v1]⟩) ⟨op1, [u2, v2]⟩).getD k.val false =
      (stepW (stepW (List.ofFn xA2) ⟨op0, [u1, v1]⟩) ⟨op1, [u2, v2]⟩).getD k.val false)
    (hApm : pm3 xA1 ≠ pm3 xA2)
    (hB2 : ∀ k : Fin 11, k.val ≠ v1 →
      (stepW (stepW (List.ofFn xB1) ⟨op0, [u1, v1]⟩) ⟨op1, [u2, v2]⟩).getD k.val false =
      (stepW (stepW (List.ofFn xB2) ⟨op0, [u1, v1]⟩) ⟨op1, [u2, v2]⟩).getD k.val false)
    (hBpm : pm3 xB1 ≠ pm3 xB2)
    (hC2 : ∀ k : Fin 11, k.val ≠ u2 →
      (stepW (stepW (List.ofFn xC1) ⟨op0, [u1, v1]⟩) ⟨op1, [u2, v2]⟩).getD k.val false =
      (stepW (stepW (List.ofFn xC2) ⟨op0, [u1, v1]⟩) ⟨op1, [u2, v2]⟩).getD k.val false)
    (hCpm : pm3 xC1 ≠ pm3 xC2)
    (hD2 : ∀ k : Fin 11, k.val ≠ v2 →
      (stepW (stepW (List.ofFn xD1) ⟨op0, [u1, v1]⟩) ⟨op1, [u2, v2]⟩).getD k.val false =
      (stepW (stepW (List.ofFn xD2) ⟨op0, [u1, v1]⟩) ⟨op1, [u2, v2]⟩).getD k.val false)
    (hDpm : pm3 xD1 ≠ pm3 xD2) :
    ¬ (∃ C : Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x) ∧
      C.output + 1 = 9 + C.size ∧
      (∀ j : Fin C.gates.length,
        ((C.gates.get j).op = GateOp.not ∧
            ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
        (((C.gates.get j).op = GateOp.and ∨
            (C.gates.get j).op = GateOp.or) ∧
            ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
      (∀ j : Fin C.gates.length,
        (∃ x y : Fin 9 → Bool,
          (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
        ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
          (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
      (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
        ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
      C.gates.head? = some ⟨op0, [u1, v1]⟩ ∧
      C.gates.tail.head? = some ⟨op1, [u2, v2]⟩) := by
  rintro ⟨C, _, hsize, heval, hout, hform, _, hused, hhead, htail⟩
  have hS : C.gates.length ≤ 11 := hsize
  cases hgs : C.gates with
  | nil => simp [hgs] at hhead
  | cons g0 tail0 =>
    simp only [hgs, List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases htl : tail0 with
    | nil => simp [hgs, htl] at htail
    | cons g1 rest =>
      simp only [hgs, htl, List.tail_cons, List.head?_cons, Option.some.injEq] at htail
      subst htail
      have hlen_ge : 2 ≤ C.gates.length := by simp [hgs, htl]
      have hout_val : C.output = 8 + C.gates.length := by
        have : C.size = C.gates.length := rfl
        omega
      let allIn : List ℕ := C.gates.flatMap (fun g => g.inputs)
      have hall_lt : ∀ w ∈ allIn, w < 8 + C.gates.length := by
        intro w hw
        rcases List.mem_flatMap.mp hw with ⟨g, hg, hwg⟩
        rcases List.mem_iff_get.mp hg with ⟨j, rfl⟩
        rcases hform j with ⟨_, a, ha, hin⟩ | ⟨_, a, b, hab, hb, hin⟩
        · rw [hin] at hwg
          simp only [List.mem_singleton] at hwg
          subst hwg
          omega
        · rw [hin] at hwg
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwg
          rcases hwg with rfl | rfl <;> omega
      have hlen_le : allIn.length ≤ 2 * C.gates.length := by
        apply flatMap_len_le
        intro g hg
        rcases List.mem_iff_get.mp hg with ⟨j, rfl⟩
        rcases hform j with ⟨_, a, _, hin⟩ | ⟨_, a, b, _, _, hin⟩
        · rw [List.get_eq_getElem] at hin; simp [hin]
        · rw [List.get_eq_getElem] at hin; simp [hin]
      have hcount_ge1 : ∀ w, w < 8 + C.gates.length → 1 ≤ allIn.count w := by
        intro w hw
        by_cases hw9 : w < 9
        · by_contra hlt
          have hc0 : allIn.count w = 0 := by omega
          have hnotmem : ∀ g ∈ C.gates, w ∉ g.inputs := by
            intro g hg hwg
            have : w ∈ allIn := List.mem_flatMap.mpr ⟨g, hg, hwg⟩
            have : 0 < allIn.count w := List.count_pos_iff.mpr this
            omega
          rcases pm3_depends_on ⟨w, hw9⟩ with ⟨x1, x2, hagr, hneq⟩
          have h12 := evalW_agree_except C.gates w (List.ofFn x1) (List.ofFn x2)
            (by simp)
            (fun k hk => by
              rw [ofFn_getD_eq, ofFn_getD_eq]
              by_cases hk9 : k < 9
              · simp only [hk9, ↓reduceDIte]
                exact hagr ⟨k, hk9⟩ (fun heq => hk (congrArg Fin.val heq))
              · simp [hk9])
            hnotmem
          have hce : C.eval (List.ofFn x1) = C.eval (List.ofFn x2) := by
            rw [eval_eq_evalW, eval_eq_evalW]
            exact h12.2 C.output (by omega)
          rw [heval x1, heval x2] at hce
          exact hneq hce
        · have hj : w - 9 < C.gates.length := by omega
          have hj1 : w - 9 + 1 < C.gates.length := by omega
          rcases hused ⟨w - 9, hj⟩ hj1 with ⟨k, _, hmem⟩
          have heqw : 9 + (w - 9) = w := by omega
          rw [heqw] at hmem
          have : w ∈ allIn := List.mem_flatMap.mpr ⟨C.gates.get k, List.get_mem _ _, hmem⟩
          exact List.count_pos_iff.mpr this
      have hgs2 : C.gates = ⟨op0, [u1, v1]⟩ :: ⟨op1, [u2, v2]⟩ :: rest := by rw [hgs, htl]
      have hA_rest := in_rest_of_agree _ _ rest C hgs2 heval u1 (by omega) xA1 xA2 hA2 hApm
      have hB_rest := in_rest_of_agree _ _ rest C hgs2 heval v1 (by omega) xB1 xB2 hB2 hBpm
      have hC_rest := in_rest_of_agree _ _ rest C hgs2 heval u2 (by omega) xC1 xC2 hC2 hCpm
      have hD_rest := in_rest_of_agree _ _ rest C hgs2 heval v2 (by omega) xD1 xD2 hD2 hDpm
      have hsplit : allIn = u1 :: v1 :: u2 :: v2 :: rest.flatMap (fun g => g.inputs) := by
        simp [allIn, hgs2]
      have hcu1 : 2 ≤ allIn.count u1 := by
        rcases hA_rest with ⟨g, hg, hgu⟩
        have hpos : 0 < (rest.flatMap (fun g => g.inputs)).count u1 :=
          List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨g, hg, hgu⟩)
        rw [hsplit]
        simp only [List.count_cons, beq_self_eq_true, beq_iff_eq, ↓reduceIte]
        omega
      have hcv1 : 2 ≤ allIn.count v1 := by
        rcases hB_rest with ⟨g, hg, hgv⟩
        have hpos : 0 < (rest.flatMap (fun g => g.inputs)).count v1 :=
          List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨g, hg, hgv⟩)
        rw [hsplit]
        simp only [List.count_cons, beq_self_eq_true, beq_iff_eq, ↓reduceIte]
        omega
      have hcu2 : 2 ≤ allIn.count u2 := by
        rcases hC_rest with ⟨g, hg, hgu⟩
        have hpos : 0 < (rest.flatMap (fun g => g.inputs)).count u2 :=
          List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨g, hg, hgu⟩)
        rw [hsplit]
        simp only [List.count_cons, beq_self_eq_true, beq_iff_eq, ↓reduceIte]
        omega
      have hcv2 : 2 ≤ allIn.count v2 := by
        rcases hD_rest with ⟨g, hg, hgv⟩
        have hpos : 0 < (rest.flatMap (fun g => g.inputs)).count v2 :=
          List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨g, hg, hgv⟩)
        rw [hsplit]
        simp only [List.count_cons, beq_self_eq_true, beq_iff_eq, ↓reduceIte]
        omega
      have hsum_eq : allIn.length = ∑ w ∈ Finset.range (8 + C.gates.length), allIn.count w :=
        list_length_eq_sum_count allIn (8 + C.gates.length) hall_lt
      have hsum_lb : (∑ w ∈ Finset.range (8 + C.gates.length),
          (1 + (if w = u1 then 1 else 0) + (if w = v1 then 1 else 0) +
           (if w = u2 then 1 else 0) + (if w = v2 then 1 else 0))) ≤
          ∑ w ∈ Finset.range (8 + C.gates.length), allIn.count w := by
        apply Finset.sum_le_sum
        intro w hw
        have hwlt : w < 8 + C.gates.length := Finset.mem_range.mp hw
        have h1 := hcount_ge1 w hwlt
        by_cases hw1 : w = u1
        · subst hw1; simp only [hu1v1, hu1u2, hu1v2, ↓reduceIte]; omega
        · by_cases hw2 : w = v1
          · subst hw2; simp only [hu1v1.symm, hv1u2, hv1v2, ↓reduceIte]; omega
          · by_cases hw3 : w = u2
            · subst hw3; simp only [hu1u2.symm, hv1u2.symm, hu2v2, ↓reduceIte]; omega
            · by_cases hw4 : w = v2
              · subst hw4; simp only [hu1v2.symm, hv1v2.symm, hu2v2.symm, ↓reduceIte]; omega
              · simp only [hw1, hw2, hw3, hw4, ↓reduceIte]; omega
      have hu1_mem : u1 ∈ Finset.range (8 + C.gates.length) := Finset.mem_range.mpr (by omega)
      have hv1_mem : v1 ∈ Finset.range (8 + C.gates.length) := Finset.mem_range.mpr (by omega)
      have hu2_mem : u2 ∈ Finset.range (8 + C.gates.length) := Finset.mem_range.mpr (by omega)
      have hv2_mem : v2 ∈ Finset.range (8 + C.gates.length) := Finset.mem_range.mpr (by omega)
      have hsum_calc : (∑ w ∈ Finset.range (8 + C.gates.length),
          (1 + (if w = u1 then 1 else 0) + (if w = v1 then 1 else 0) +
           (if w = u2 then 1 else 0) + (if w = v2 then 1 else 0))) =
          (8 + C.gates.length) + 1 + 1 + 1 + 1 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
          Finset.sum_ite_eq', hu1_mem, hv1_mem, hu2_mem, hv2_mem, ↓reduceIte]
      omega

end PEqualNP.Outside.L_meta_27209

theorem PEqualNP.Outside.L_meta_27209 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩)) :=
  PEqualNP.Outside.L_meta_27209.no_circuit_disjoint_bin 0 4 2 8
    PEqualNP.CircuitLowerBounds.GateOp.and PEqualNP.CircuitLowerBounds.GateOp.and
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (PEqualNP.Outside.L_meta_27209.mkX false false false false false true false true false)
    (PEqualNP.Outside.L_meta_27209.mkX true false false false false true false true false)
    (PEqualNP.Outside.L_meta_27209.mkX false false true false false false true false false)
    (PEqualNP.Outside.L_meta_27209.mkX false false true false true false true false false)
    (PEqualNP.Outside.L_meta_27209.mkX false false false false true false true false false)
    (PEqualNP.Outside.L_meta_27209.mkX false false true false true false true false false)
    (PEqualNP.Outside.L_meta_27209.mkX true false false false true false false false false)
    (PEqualNP.Outside.L_meta_27209.mkX true false false false true false false false true)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
