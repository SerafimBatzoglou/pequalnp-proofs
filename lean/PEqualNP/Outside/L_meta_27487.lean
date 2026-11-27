import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27487

open PEqualNP.CircuitLowerBounds

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

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
      · rw [if_pos h1, if_pos h1]
        exact hagr k hk
      · rw [if_neg h1, if_neg h1]
    exact ih (stepW w1 g) (stepW w2 g) hstep_len hstep_agr (fun g' hg' => hno g' (List.mem_cons_of_mem g hg'))

theorem evalW_mono_except0 (gs : List Gate) :
    ∀ (w1 w2 : List Bool),
      w1.length = w2.length →
      (∀ k, k ≠ 0 → w1.getD k false = true → w2.getD k false = true) →
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ 0 ∉ g.inputs) →
      (evalW gs w1).length = (evalW gs w2).length ∧
      (∀ k, k ≠ 0 → (evalW gs w1).getD k false = true → (evalW gs w2).getD k false = true) := by
  induction gs with
  | nil =>
    intro w1 w2 hlen hmono _
    exact ⟨hlen, hmono⟩
  | cons g rest ih =>
    intro w1 w2 hlen hmono hgood
    have ⟨hop, hno0⟩ := hgood g (List.mem_cons_self ..)
    have hval : g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
        g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
      intro ht
      rcases hop with hand | hor
      · rw [hand] at ht ⊢
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂] at ht ⊢
        intro i hi
        exact hmono i (fun h0 => hno0 (h0 ▸ hi)) (ht i hi)
      · rw [hor] at ht ⊢
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at ht ⊢
        rcases ht with ⟨_, ⟨i, hi, rfl⟩, hti⟩
        exact ⟨w2.getD i false, ⟨i, hi, rfl⟩, hmono i (fun h0 => hno0 (h0 ▸ hi)) hti⟩
    have hstep_len : (stepW w1 g).length = (stepW w2 g).length := by
      simp [stepW, hlen]
    have hstep_mono : ∀ k, k ≠ 0 → (stepW w1 g).getD k false = true → (stepW w2 g).getD k false = true := by
      intro k hk ht
      simp only [stepW, getD_append_right_single, hlen] at ht ⊢
      by_cases h1 : k < w2.length
      · rw [if_pos h1] at ht ⊢
        exact hmono k hk ht
      · rw [if_neg h1] at ht ⊢
        by_cases h2 : k = w2.length
        · rw [if_pos h2] at ht ⊢
          exact hval ht
        · rw [if_neg h2] at ht
          exact Bool.noConfusion ht
    exact ih (stepW w1 g) (stepW w2 g) hstep_len hstep_mono (fun g' hg' => hgood g' (List.mem_cons_of_mem g hg'))

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

theorem flatMap_len_add_not (gs : List Gate)
    (h : ∀ g ∈ gs, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) :
    (gs.flatMap (fun g => g.inputs)).length + gs.countP (fun g => isNot g.op) = 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g t ih =>
    have hg := h g (List.mem_cons_self ..)
    have ht := ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))
    simp only [List.flatMap_cons, List.length_append, List.countP_cons, List.length_cons]
    rcases hg with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
    · have hnot : isNot g.op = true := by rw [hop]; rfl
      rw [hnot, hlen]; simp only [↓reduceIte]; omega
    · rcases hop with hand | hor
      · have hnot : isNot g.op = false := by rw [hand]; rfl
        rw [hnot, hlen]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · have hnot : isNot g.op = false := by rw [hor]; rfl
        rw [hnot, hlen]; simp only [Bool.false_eq_true, ↓reduceIte]; omega

theorem ofFn_getD_eq (x : Fin 9 → Bool) (k : ℕ) :
    (List.ofFn x).getD k false = if hk : k < 9 then x ⟨k, hk⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases hk : k < 9
  · simp [hk]
  · simp [hk]

theorem stepW_ofFn_getD_lt (x : Fin 9 → Bool) (g : Gate) (k : ℕ) (hk : k < 9) :
    (stepW (List.ofFn x) g).getD k false = x ⟨k, hk⟩ := by
  rw [stepW, getD_append_right_single]
  have hlen : (List.ofFn x).length = 9 := List.length_ofFn
  rw [hlen, if_pos hk, ofFn_getD_eq, dif_pos hk]

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

theorem no_circuit_not0_bin (u v : ℕ) (op1 : GateOp)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v) (hu9 : u < 9) (hv9 : v < 9)
    (xU1 xU2 : Fin 9 → Bool)
    (hxU_agr : ∀ k : Fin 9, k.val ≠ u → xU1 k = xU2 k)
    (hxU_v : op1.eval [xU1 ⟨u, hu9⟩, xU1 ⟨v, hv9⟩] = op1.eval [xU2 ⟨u, hu9⟩, xU2 ⟨v, hv9⟩])
    (hxU_pm : pm3 xU1 ≠ pm3 xU2)
    (xV1 xV2 : Fin 9 → Bool)
    (hxV_agr : ∀ k : Fin 9, k.val ≠ v → xV1 k = xV2 k)
    (hxV_u : op1.eval [xV1 ⟨u, hu9⟩, xV1 ⟨v, hv9⟩] = op1.eval [xV2 ⟨u, hu9⟩, xV2 ⟨v, hv9⟩])
    (hxV_pm : pm3 xV1 ≠ pm3 xV2) :
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
      C.gates.head? = some ⟨GateOp.not, [0]⟩ ∧
      C.gates.tail.head? = some ⟨op1, [u, v]⟩) := by
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
      have hlen_eq : allIn.length + C.gates.countP (fun g => isNot g.op) = 2 * C.gates.length := by
        apply flatMap_len_add_not
        intro g hg
        rcases List.mem_iff_get.mp hg with ⟨j, rfl⟩
        rcases hform j with ⟨hop, a, _, hin⟩ | ⟨hop, a, b, _, _, hin⟩
        · left; exact ⟨hop, by rw [List.get_eq_getElem] at hin; simp [hin]⟩
        · right; exact ⟨hop, by rw [List.get_eq_getElem] at hin; simp [hin]⟩
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
      have hu_rest : ∃ g ∈ rest, u ∈ g.inputs := by
        by_contra hno
        push_neg at hno
        let w0_1 := List.ofFn xU1
        let w0_2 := List.ofFn xU2
        let w1_1 := stepW w0_1 ⟨GateOp.not, [0]⟩
        let w1_2 := stepW w0_2 ⟨GateOp.not, [0]⟩
        let w2_1 := stepW w1_1 ⟨op1, [u, v]⟩
        let w2_2 := stepW w1_2 ⟨op1, [u, v]⟩
        have hw0_agr : ∀ k, k ≠ u → w0_1.getD k false = w0_2.getD k false := by
          intro k hk
          simp only [w0_1, w0_2, ofFn_getD_eq]
          by_cases hk9 : k < 9
          · simp only [hk9, ↓reduceDIte]
            exact hxU_agr ⟨k, hk9⟩ hk
          · simp [hk9]
        have hw1_agr : ∀ k, k ≠ u → w1_1.getD k false = w1_2.getD k false := by
          have h12 := evalW_agree_except [⟨GateOp.not, [0]⟩] u w0_1 w0_2 (by simp [w0_1, w0_2]) hw0_agr
            (by simp [hu0])
          exact h12.2
        have hw1_len1 : w1_1.length = 10 := by simp [w1_1, w0_1, stepW]
        have hw1_len2 : w1_2.length = 10 := by simp [w1_2, w0_2, stepW]
        have hw1_u1 : w1_1.getD u false = xU1 ⟨u, hu9⟩ := stepW_ofFn_getD_lt xU1 _ u hu9
        have hw1_v1 : w1_1.getD v false = xU1 ⟨v, hv9⟩ := stepW_ofFn_getD_lt xU1 _ v hv9
        have hw1_u2 : w1_2.getD u false = xU2 ⟨u, hu9⟩ := stepW_ofFn_getD_lt xU2 _ u hu9
        have hw1_v2 : w1_2.getD v false = xU2 ⟨v, hv9⟩ := stepW_ofFn_getD_lt xU2 _ v hv9
        have hw2_agr : ∀ k, k ≠ u → w2_1.getD k false = w2_2.getD k false := by
          intro k hk
          simp only [w2_1, w2_2, stepW, getD_append_right_single, hw1_len1, hw1_len2,
            List.map_cons, List.map_nil, hw1_u1, hw1_v1, hw1_u2, hw1_v2, hxU_v]
          by_cases h1 : k < 10
          · rw [if_pos h1, if_pos h1]
            exact hw1_agr k hk
          · rw [if_neg h1, if_neg h1]
        have hw2_len : w2_1.length = w2_2.length := by
          simp [w2_1, w2_2, stepW, hw1_len1, hw1_len2]
        have hres := evalW_agree_except rest u w2_1 w2_2 hw2_len hw2_agr hno
        have hce : C.eval (List.ofFn xU1) = C.eval (List.ofFn xU2) := by
          rw [eval_eq_evalW, eval_eq_evalW, hgs, htl]
          exact hres.2 C.output (by omega)
        rw [heval xU1, heval xU2] at hce
        exact hxU_pm hce
      have hv_rest : ∃ g ∈ rest, v ∈ g.inputs := by
        by_contra hno
        push_neg at hno
        let w0_1 := List.ofFn xV1
        let w0_2 := List.ofFn xV2
        let w1_1 := stepW w0_1 ⟨GateOp.not, [0]⟩
        let w1_2 := stepW w0_2 ⟨GateOp.not, [0]⟩
        let w2_1 := stepW w1_1 ⟨op1, [u, v]⟩
        let w2_2 := stepW w1_2 ⟨op1, [u, v]⟩
        have hw0_agr : ∀ k, k ≠ v → w0_1.getD k false = w0_2.getD k false := by
          intro k hk
          simp only [w0_1, w0_2, ofFn_getD_eq]
          by_cases hk9 : k < 9
          · simp only [hk9, ↓reduceDIte]
            exact hxV_agr ⟨k, hk9⟩ hk
          · simp [hk9]
        have hw1_agr : ∀ k, k ≠ v → w1_1.getD k false = w1_2.getD k false := by
          have h12 := evalW_agree_except [⟨GateOp.not, [0]⟩] v w0_1 w0_2 (by simp [w0_1, w0_2]) hw0_agr
            (by simp [hv0])
          exact h12.2
        have hw1_len1 : w1_1.length = 10 := by simp [w1_1, w0_1, stepW]
        have hw1_len2 : w1_2.length = 10 := by simp [w1_2, w0_2, stepW]
        have hw1_u1 : w1_1.getD u false = xV1 ⟨u, hu9⟩ := stepW_ofFn_getD_lt xV1 _ u hu9
        have hw1_v1 : w1_1.getD v false = xV1 ⟨v, hv9⟩ := stepW_ofFn_getD_lt xV1 _ v hv9
        have hw1_u2 : w1_2.getD u false = xV2 ⟨u, hu9⟩ := stepW_ofFn_getD_lt xV2 _ u hu9
        have hw1_v2 : w1_2.getD v false = xV2 ⟨v, hv9⟩ := stepW_ofFn_getD_lt xV2 _ v hv9
        have hw2_agr : ∀ k, k ≠ v → w2_1.getD k false = w2_2.getD k false := by
          intro k hk
          simp only [w2_1, w2_2, stepW, getD_append_right_single, hw1_len1, hw1_len2,
            List.map_cons, List.map_nil, hw1_u1, hw1_v1, hw1_u2, hw1_v2, hxV_u]
          by_cases h1 : k < 10
          · rw [if_pos h1, if_pos h1]
            exact hw1_agr k hk
          · rw [if_neg h1, if_neg h1]
        have hw2_len : w2_1.length = w2_2.length := by
          simp [w2_1, w2_2, stepW, hw1_len1, hw1_len2]
        have hres := evalW_agree_except rest v w2_1 w2_2 hw2_len hw2_agr hno
        have hce : C.eval (List.ofFn xV1) = C.eval (List.ofFn xV2) := by
          rw [eval_eq_evalW, eval_eq_evalW, hgs, htl]
          exact hres.2 C.output (by omega)
        rw [heval xV1, heval xV2] at hce
        exact hxV_pm hce
      have hcu : 2 ≤ allIn.count u := by
        rcases hu_rest with ⟨g, hg, hgu⟩
        have hpos : 0 < (rest.flatMap (fun g => g.inputs)).count u :=
          List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨g, hg, hgu⟩)
        have hsplit : allIn = 0 :: u :: v :: rest.flatMap (fun g => g.inputs) := by
          simp [allIn, hgs, htl]
        rw [hsplit]
        simp only [List.count_cons, beq_self_eq_true, beq_iff_eq, ↓reduceIte]
        omega
      have hcv : 2 ≤ allIn.count v := by
        rcases hv_rest with ⟨g, hg, hgv⟩
        have hpos : 0 < (rest.flatMap (fun g => g.inputs)).count v :=
          List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨g, hg, hgv⟩)
        have hsplit : allIn = 0 :: u :: v :: rest.flatMap (fun g => g.inputs) := by
          simp [allIn, hgs, htl]
        rw [hsplit]
        simp only [List.count_cons, beq_self_eq_true, beq_iff_eq, ↓reduceIte]
        omega
      have hsum_eq : allIn.length = ∑ w ∈ Finset.range (8 + C.gates.length), allIn.count w :=
        list_length_eq_sum_count allIn (8 + C.gates.length) hall_lt
      have hsum_lb : (∑ w ∈ Finset.range (8 + C.gates.length),
          (1 + (if w = u then 1 else 0) + (if w = v then 1 else 0) +
           (if w = 0 then allIn.count 0 - 1 else 0))) ≤
          ∑ w ∈ Finset.range (8 + C.gates.length), allIn.count w := by
        apply Finset.sum_le_sum
        intro w hw
        have hwlt : w < 8 + C.gates.length := Finset.mem_range.mp hw
        have h1 := hcount_ge1 w hwlt
        by_cases hwu : w = u
        · subst hwu; simp only [hu0, huv, ↓reduceIte]; omega
        · by_cases hwv : w = v
          · subst hwv; simp only [hv0, huv.symm, ↓reduceIte]; omega
          · by_cases hw0 : w = 0
            · subst hw0; simp only [hu0.symm, hv0.symm, ↓reduceIte]; omega
            · simp only [hwu, hwv, hw0, ↓reduceIte]; omega
      have h0_mem : 0 ∈ Finset.range (8 + C.gates.length) := Finset.mem_range.mpr (by omega)
      have hu_mem : u ∈ Finset.range (8 + C.gates.length) := Finset.mem_range.mpr (by omega)
      have hv_mem : v ∈ Finset.range (8 + C.gates.length) := Finset.mem_range.mpr (by omega)
      have hsum_calc : (∑ w ∈ Finset.range (8 + C.gates.length),
          (1 + (if w = u then 1 else 0) + (if w = v then 1 else 0) +
           (if w = 0 then allIn.count 0 - 1 else 0))) =
          (8 + C.gates.length) + 1 + 1 + (allIn.count 0 - 1) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
          Finset.sum_ite_eq', h0_mem, hu_mem, hv_mem, ↓reduceIte]
      have hc0_ge1 : 1 ≤ allIn.count 0 := hcount_ge1 0 (by omega)
      have hnot_split : C.gates.countP (fun g => isNot g.op) =
          1 + (⟨op1, [u, v]⟩ :: rest).countP (fun g => isNot g.op) := by
        rw [hgs, htl, List.countP_cons]
        simp only [isNot, ↓reduceIte]
        omega
      have h0_split : allIn.count 0 =
          1 + ((⟨op1, [u, v]⟩ :: rest).flatMap (fun g => g.inputs)).count 0 := by
        have hsp : allIn = 0 :: ((⟨op1, [u, v]⟩ :: rest).flatMap (fun g => g.inputs)) := by
          simp only [allIn, hgs, htl, List.flatMap_cons, List.cons_append, List.nil_append]
        rw [hsp, List.count_cons]
        simp only [beq_self_eq_true, ↓reduceIte]
        omega
      have htail_not0 : (⟨op1, [u, v]⟩ :: rest).countP (fun g => isNot g.op) = 0 := by omega
      have htail_in0 : ((⟨op1, [u, v]⟩ :: rest).flatMap (fun g => g.inputs)).count 0 = 0 := by omega
      have htail_good : ∀ g ∈ (⟨op1, [u, v]⟩ :: rest),
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ 0 ∉ g.inputs := by
        intro g hg
        have hgC : g ∈ C.gates := by simp [hgs, htl, hg]
        have hnot_ne : g.op ≠ GateOp.not := by
          intro heq
          have : 0 < (⟨op1, [u, v]⟩ :: rest).countP (fun g => isNot g.op) :=
            List.countP_pos_iff.mpr ⟨g, hg, by rw [heq]; rfl⟩
          omega
        have hop_ao : g.op = GateOp.and ∨ g.op = GateOp.or := by
          rcases List.mem_iff_get.mp hgC with ⟨j, rfl⟩
          rcases hform j with ⟨h1, _⟩ | ⟨h2, _⟩
          · exact absurd h1 hnot_ne
          · exact h2
        have hno0 : 0 ∉ g.inputs := by
          intro hmem
          have : 0 < ((⟨op1, [u, v]⟩ :: rest).flatMap (fun g => g.inputs)).count 0 :=
            List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨g, hg, hmem⟩)
          omega
        exact ⟨hop_ao, hno0⟩
      let y1 := mkX true false false false true false false false true
      let y2 := mkX false false false false true false false false true
      let s1 := stepW (List.ofFn y1) ⟨GateOp.not, [0]⟩
      let s2 := stepW (List.ofFn y2) ⟨GateOp.not, [0]⟩
      have hs_len : s1.length = s2.length := by simp [s1, s2, stepW]
      have hs_mono : ∀ k, k ≠ 0 → s1.getD k false = true → s2.getD k false = true := by
        intro k hk ht
        by_cases hk10 : k < 10
        · interval_cases k <;> simp_all [s1, s2, y1, y2, mkX, stepW, GateOp.eval]
        · have hge : s1.length ≤ k := by simp [s1, stepW]; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at ht
      have hm := evalW_mono_except0 (⟨op1, [u, v]⟩ :: rest) s1 s2 hs_len hs_mono htail_good
      have hce1 : C.eval (List.ofFn y1) = true := by rw [heval y1]; decide
      have hce2 : C.eval (List.ofFn y2) = false := by rw [heval y2]; decide
      have hle : C.eval (List.ofFn y1) = true → C.eval (List.ofFn y2) = true := by
        rw [eval_eq_evalW, eval_eq_evalW, hgs, htl]
        exact hm.2 C.output (by omega)
      have := hle hce1
      rw [hce2] at this
      exact Bool.noConfusion this

end PEqualNP.Outside.L_meta_27487

theorem PEqualNP.Outside.L_meta_27487 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩)) :=
  PEqualNP.Outside.L_meta_27487.no_circuit_not0_bin 4 5 PEqualNP.CircuitLowerBounds.GateOp.or
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (PEqualNP.Outside.L_meta_27487.mkX false false true false false true true false false)
    (PEqualNP.Outside.L_meta_27487.mkX false false true false true true true false false)
    (by decide) (by decide) (by decide)
    (PEqualNP.Outside.L_meta_27487.mkX true false false false true false false true false)
    (PEqualNP.Outside.L_meta_27487.mkX true false false false true true false true false)
    (by decide) (by decide) (by decide)
