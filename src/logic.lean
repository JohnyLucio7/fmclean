
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
intro p, -- Suponha P
intro np, -- Suponha ¬P
contradiction, -- Contradição
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro p, -- Suponha ¬¬p 
  by_cases h : P, -- "Aplicando feitiço" LEM
  assumption,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro p,
  by_cases h : P,
  assumption,
  contradiction,
  intro q,
  intro q1,
  contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro hp,
  cases hp,
  right,
  assumption,
  left,
  assumption,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro hp,
  split,
  cases hp,
  assumption,
  cases hp,
  assumption,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro hp,
  cases hp,
  intro hhp,
  contradiction,
  intro hhp,
  assumption,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro hp,
  cases hp,
  intro hhp,
  contradiction,
  intro hhp,
  assumption,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hp,
  intro hhp,
  intro hhhp,
  have hq : Q := hp hhhp,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro h,
  intro hp,
  by_contradiction hboom,
  have np : ¬P := h hboom,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro piq,
  intro nq,
  intro p,
  have q : Q := piq p,
  contradiction,
  intro nqinp,
  intro p,
  by_contradiction hboom,
  have np : ¬P := nqinp hboom,
  contradiction,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro n_pounp,
  apply n_pounp,
  left,
  by_contradiction hboom,
  apply n_pounp,
  right,
  assumption,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro piqip,
  by_cases npoup : P,
  intro np,
  contradiction,
  intro np,
  apply np,
  apply piqip,
  intro p,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro pouq,
  cases pouq,
  intro npenq,
  cases npenq,
  contradiction,
  intro npenq,
  cases npenq,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro peq,
  cases peq,
  intro npounq,
  cases npounq,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro n_pouq,
  split,
  intro p,
  apply n_pouq,
  left,
  by_contradiction hboom,
  contradiction,
  intro nq,
  apply n_pouq,
  right,
  by_contradiction,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro npenq,
  intro n_pouq,
  cases n_pouq,
  cases npenq,
  contradiction,
  cases npenq,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro n_peq,
  by_cases h : P,
  left,
  intro p,
  apply n_peq,
  split,
  assumption,
  assumption,
  right,
  assumption,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nqounp,
  intro n_peq,
  cases n_peq,
  cases nqounp,
  contradiction,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  apply demorgan_conj,
  apply demorgan_conj_converse,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro n_pouq,
  split,
  intro p,
  apply n_pouq,
  left,
  assumption,
  intro q,
  apply n_pouq,
  right,
  assumption,
  intro npenq,
  intro pouq,
  cases npenq,
  cases pouq,
  contradiction,
  contradiction,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro pe_qour,
  cases pe_qour,
  cases pe_qour_right,
  left,
  split,
  assumption,
  assumption,
  right,
  split,
  assumption,
  assumption,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro peq_ou_per,
  cases peq_ou_per,
  cases peq_ou_per,
  split,
  assumption,
  left,
  assumption,
  cases peq_ou_per,
  split,
  assumption,
  right,
  assumption,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro pou_qer,
  cases pou_qer,
  split,
  left,
  assumption,
  left,
  assumption,
  cases pou_qer,
  split,
  right,
  assumption,
  right,
  assumption,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro pouq_e_pour,
  cases pouq_e_pour,
  cases pouq_e_pour_left,
  left,
  assumption,
  cases pouq_e_pour_right,
  left,
  assumption,
  right,
  split,
  assumption,
  assumption,

end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro peqir,
  intro p,
  intro q,
  apply peqir,
  split,
  assumption,
  assumption,  
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro pi_qir,
  intro peq,
  cases peq,
  apply pi_qir,
  assumption,
  assumption,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  assumption,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  assumption,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  assumption,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro peq,
  cases peq,
  assumption,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro peq,
  cases peq,
  assumption,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pep,
  cases pep,
  assumption,
  intro p,
  split,
  assumption,
  assumption,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro poup,
  cases poup,
  assumption,
  assumption,
  intro p,
  left,
  assumption,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro ex_px,
  intro a,
  intro h,
  apply ex_px,
  existsi a,
  assumption,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro Vx_nPx,
  intro ex_px,
  cases ex_px with a U,
  apply Vx_nPx a,
  assumption,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro Vx_px,
  by_contradiction hboom,
  apply Vx_px,
  intro a,
  by_contradiction,
  apply hboom,
  existsi a,
  assumption,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro Ex_nPx,
  intro Vx_px,
  cases Ex_nPx with a Pa,
  apply Pa,
  apply Vx_px a,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  apply demorgan_forall,
  apply demorgan_forall_converse,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  intro nEx_Px,
  intro a,
  by_contradiction,
  apply nEx_Px,
  existsi a,
  assumption,
  intro Vx_nPx,
  intro Ex_Px,
  cases Ex_Px with a U,
  apply Vx_nPx a,
  assumption,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro Ex_Px,
  intro Vx_nPx,
  cases Ex_Px with a Pa,
  apply Vx_nPx a,
  assumption,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro Vx_Px,
  intro Ex_nPx,
  cases Ex_nPx with a Pa,
  apply Pa,
  apply Vx_Px a,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro nEx_nPx,
  intro a,
  by_contradiction,
  apply nEx_nPx,
  existsi a,
  assumption,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro nVx_nPx,
  by_contradiction,
  apply nVx_nPx,
  intro a,
  intro Pa,
  apply h,
  existsi a,
  assumption,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  apply forall_as_neg_exists,
  apply forall_as_neg_exists_converse,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  apply exists_as_neg_forall,
  apply exists_as_neg_forall_converse,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro Ex_PxeQx,
  split,
  by_contradiction hboom,
  cases Ex_PxeQx with a PaeQa,
  apply hboom,
  existsi a,
  cases PaeQa,
  assumption,
  by_contradiction hboom,
  cases Ex_PxeQx with a PaeQa,
  apply hboom,
  existsi a,
  cases PaeQa,
  assumption,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro Ex_PxouQx,
  cases Ex_PxouQx with a PaouQa,
  cases PaouQa,
  left,
  existsi a,
  assumption,
  right,
  existsi a,
  assumption,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro Ex_Px_ou_Ex_Qx,
  cases Ex_Px_ou_Ex_Qx with Px_ou_Qx,
  by_contradiction hboom,
  cases Px_ou_Qx with a Pa,
  apply hboom,
  existsi a,
  left,
  assumption,
  by_contradiction hboom,
  cases Ex_Px_ou_Ex_Qx with a Qa,
  apply hboom,
  existsi a,
  right,
  assumption,
  
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro Vx_PxeQx,
  split,
  intro a,
  apply (Vx_PxeQx a).left,
  intro a,
  apply (Vx_PxeQx a).right,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro Vx_Px_e_Vx_Qx,
  intro a,
  cases Vx_Px_e_Vx_Qx with l r,
  split,
  apply l a,
  apply r a,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro Vx_Px_ou_Vx_Qx,
  intro a,
  cases Vx_Px_ou_Vx_Qx with l r,
  left,
  apply l a,
  right,
  apply r a,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
