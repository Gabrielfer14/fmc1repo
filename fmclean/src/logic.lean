
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hp,
  apply not_not_intro,
  assumption,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hp,
  by_contradiction h,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  { intro hp,
    apply doubleneg_elim,
    assumption,
  },
  {intro hp,
  apply doubleneg_intro,
  assumption,
  }
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro hor,
  cases hor with hp hq,
  { right,
    assumption,
  },
  { left,
    assumption,
  }
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro h,
  cases h with hp hq,
  split,
  { 
    assumption,
  },
  { 
    assumption,
  }
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro pq,
  intro hp,
  cases pq with p q,
  case or.inr{
    assumption
  },
  case or.inl{
    by contradiction
  },
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro pq,
  intro hp,
  cases pq with p q,
  case or.inr{
    assumption
  },
  case or.inl{
    by contradiction
  },

end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro pq,
  intro nq,
  intro hp,
  apply nq,
  apply pq,
  assumption,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros nqnp p,
  by_cases h : Q,
  {
    assumption,
  },
  {
    by_contra,
    apply nqnp,
    assumption,
    exact p,
  },
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,{
    intro pq,
    apply impl_as_contrapositive,
    assumption,
  },
  {
    intro npnq,
    apply impl_as_contrapositive_converse,
    assumption,
  },
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P ∨ ¬P)  :=
begin
  intro npnp, 
  apply npnp,
  right,
  intro p,
  apply npnp,
  left,
  assumption,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros pqp np,
  apply np,
  apply pqp,
  intro p,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬(¬P ∧ ¬Q)  :=
begin
  intro pvq,
  cases pvq with p q,
  case or.inl{
    intro npeq,
    cases npeq with np nq,
    by contradiction,
  },
  case or.inr{
    intro npeq,
    cases npeq with np nq,
    by contradiction,
  }
end

theorem conj_as_negdisj :
  P ∧ Q → ¬(¬P ∨ ¬Q)  :=
begin
  intro peq,
  cases peq with p q,
  intro nnpvq,
  cases nnpvq with np nq,
  case or.inl{
    by contradiction,
    },
  case or.inr{
    by contradiction,
  }
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P ∨ Q) → (¬P ∧ ¬Q)  :=
begin
  intro npvnq,
  split,
  {
    intro p,
    apply npvnq,
    left,
    assumption,
  },
  {
    intro q,
    apply npvnq,
    right,
    assumption,
  }
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P ∨ Q)  :=
begin
  intro npenq,
  cases npenq with np nq,
  {
   intro pvq,
   cases pvq with p q,
   case or.inl{
    by contradiction,
   },
   case or.inr{
     by contradiction,
   }, 
  }
end

theorem demorgan_conj :
  ¬(P ∧ Q) → (¬Q ∨ ¬P)  :=
begin
  intro npeq,
  by_cases h : P,
  {
    left,
    intro q,
    apply npeq,
    split,
    assumption,
    assumption,
  },
  {
    right,
    assumption,
  }
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P ∧ Q)  :=
begin
  intro npvnq,
  cases npvnq with nq np,
  case or.inl{
    intro peq,
    cases peq with p q,
    by contradiction,
  },
  case or.inr{
    intro peq,
    cases peq with p q,
    by contradiction,
  },
end

theorem demorgan_conj_law :
  ¬(P ∧ Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,{
    intro npeq,
    apply demorgan_conj,
    assumption,
  },
  {
    intro npvnq,
    apply demorgan_conj_converse,
    assumption,
  },
end

theorem demorgan_disj_law :
  ¬(P ∨ Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,{
    intro npvq,
    apply demorgan_disj,
    assumption,
  },
  {
    intro npenq,
    apply demorgan_disj_converse,
    assumption,
  },
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  :=
begin
  intro peqvr,
  cases peqvr with p qvr,
  cases qvr with q r,
  case or.inl{
    left,
    split,{
      assumption,
    },
    {
      assumption,
    },
  },
  case or.inr{
    right,
    split,{
      assumption,
    },
    {
      assumption,
    },
  },
end

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  :=
begin
  intro peqvper,
  cases peqvper with peq per,
  case or.inl{
    split,{
      cases peq with p q,
      assumption,
    },
    {
      cases peq with p q,
      left,
      assumption,
    },
  },
  case or.inr{
    split,{
      cases per with p r,
      assumption,
    },
    {
      cases per with p r,
      right,
      assumption,
    },
  },
end

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  :=
begin
  intro pvqer,
  cases pvqer with p per,
  case or.inr{
    split,{
      cases per with q r,
      right,{
        assumption,
      },
    },
      cases per with q r,
      right,{
        assumption,
    },
  },
  case or.inl{
    split,
    left,{
      assumption,
    },
    left,{
      assumption,
    },
  },
end

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  :=
begin
  intro pvqepvr,
  cases pvqepvr with pvq pvr,
  cases pvq with p q,{
    cases pvr with p r,{
      left,
      assumption,
    },
    left,
    assumption,
  },
  case or.inr{
    cases pvr with p r,{
      case or.inl{
        left,
        assumption,
      },
    },
    case or.inr or.inr{
      right,
      split,
      assumption,
      assumption,
    },
  },
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  :=
begin
  intros peqr p q,
  apply peqr,
  split,
  assumption,
  assumption,
end

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  :=
begin
  intros pqr peq,
  cases peq with p q,
  apply pqr,
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
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P ∨ Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P ∧ Q) → P  :=
begin
  intro peq,
  cases peq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P ∧ Q) → Q  :=
begin
  intro peq,
  cases peq with p q,
  exact q,
end

theorem conj_idempot :
  (P ∧ P) ↔ P :=
begin
  split,{
    intro pep,
    cases pep with p,
    exact p,
    },
    {
      intro p,
      split,
      exact p,
      exact p,
    },
end

theorem disj_idempot :
  (P ∨ P) ↔ P  :=
begin
  split,{
    intro pvp,
    cases pvp with p p',
    case or.inl{
      exact p,
    },
    case or.inr{
      exact p',
    },
  },
  intro p'',
  right,
  exact p'',
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
  intros nexu u,
  by_contradiction boom,
  apply nexu,
  existsi u,
  assumption,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros ptxu exu,
  cases exu with u pu,
  apply ptxu,
  assumption,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  rw contrapositive_law,
  rw doubleneg_law,
  intro npx,
  intro u,
  by_contradiction boom,
  apply npx,
  existsi u,
  apply boom,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros enpx ptx,
  cases enpx with u npu,
  apply npu,
  exact ptx u,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
    split,{
      intro nptx,
      apply demorgan_forall,
      assumption,
    },
    {
      intro enpx,
      apply demorgan_forall_converse,
      assumption,
    },
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,{
    intros npex u pu,
    apply npex,
    existsi u,
    assumption, 
  },
  {
  intros ptxnp exu,
  cases exu with u pu,
  apply ptxnp,
  assumption,
  },
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros pex ptx,
  cases pex with u pu,
  apply ptx,
  assumption,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros ptx eunp,
  by_contradiction boom,
  cases eunp with u npu,
  apply npu,
  exact ptx u,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros nex u,
  by_contradiction boom,
  apply nex,
  existsi u,
  assumption,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro nptnx,
  by_contradiction boom,
  apply nptnx,
  intro u,
  by_cases h : P u,
  intro q,
  apply boom,
  split,{
    exact h
  },
  assumption,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,{
    intros ptx enx,
    cases enx with u npu,
    apply npu,
    exact ptx u,
  },
  {
    intros nenpx u,
    by_contradiction boom,
    apply nenpx,
    existsi u,
    assumption,
  },
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,{
    intros pex nptx,
    cases pex with u pu,
    apply nptx,
    exact pu,
  },
  {
    intro nptpx,
    by_contradiction boom,
    apply nptpx,
    intro u,
    by_cases h : P u,
    intro pu,
    apply boom,
    split,{
      exact h
    },
    assumption,
  },
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro expeq,
  cases expeq with u peq,{
    cases peq with pu qu,{
      split,{
        split,{
          exact pu,
        },
      },
      split,{
        exact qu,
      },
      },
    },
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro expvq,
  cases expvq with u puvqu,{
    cases puvqu with pu qu,{
      case or.inl{
        left,{
          split,{
            exact pu,
          },
        },
      },
    },
    case or.inr{
      right,{
        split,{
          exact qu,
        },
      },
    },
  },
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro epxveqx,
  cases epxveqx with epx eqx,{
    cases epx with u pu,{
      split,{
        left,{
          exact pu,
        },
      },
    },
  },
  case or.inr{
    cases eqx with u qu,{
      split,{
        right,{
          exact qu,
        },
      },
    },
  },
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro ptpeq,
  split,{
    intro u,
    by_cases h : P u,{
      assumption,
    },
    {
      sorry,
    },
  },
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intros ptpeq u,
  cases ptpeq with px qx,{
    split,{
      exact px u,
    },
    {
      exact qx u,
    },
  },
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intros ptpvq u,
  cases ptpvq with px qx,
    case or.inl{
      left,{
        exact px u,
      },
    },
    case or.inr{
      right,{
        exact qx u,
      },
    },
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
