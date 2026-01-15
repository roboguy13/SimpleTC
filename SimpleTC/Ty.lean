-- k
inductive Kind : Type where
| TyKind : Kind
deriving Repr, DecidableEq

-- Φ
inductive KindCtx : Type where
| empty : KindCtx
| extend : KindCtx → Kind → KindCtx
deriving Repr, DecidableEq

inductive InKindCtx : KindCtx → Kind → Type where
| here : ∀ {Φ k}, InKindCtx (.extend Φ k) k
| there : ∀ {Φ k k'},
    InKindCtx Φ k →
    InKindCtx (.extend Φ k') k
deriving Repr, DecidableEq

-- Φ ⊢ a : k
inductive Ty : KindCtx → Kind → Type where
| NatTy : ∀ {Φ}, Ty Φ .TyKind
| BoolTy : ∀ {Φ}, Ty Φ .TyKind
| FunTy : ∀ {Φ}, Ty Φ .TyKind → Ty Φ .TyKind → Ty Φ .TyKind
| TyVar : ∀ {Φ k},
    InKindCtx Φ k →
    Ty Φ k
| Forall : ∀ {Φ},
    (k : Kind) →
    Ty (Φ.extend k) .TyKind →
    Ty Φ .TyKind
deriving Repr, DecidableEq

inductive RawTy : Type where
| NatTy : RawTy
| BoolTy : RawTy
| TyVar : Nat → RawTy
| FunTy : RawTy → RawTy → RawTy
| Forall : Kind → RawTy → RawTy
deriving Repr, DecidableEq

def eraseTyVarKinds {Φ k} : InKindCtx Φ k → Nat
| .here => 0
| .there x => .succ (eraseTyVarKinds x)

def eraseKinds {Φ k} : Ty Φ k → RawTy
| .NatTy => .NatTy
| .BoolTy => .BoolTy
| .FunTy a b => .FunTy (eraseKinds a) (eraseKinds b)
| .TyVar x => .TyVar (eraseTyVarKinds x)
| .Forall k a => .Forall k (eraseKinds a)

inductive KindCheckError : Type where
| tyVarOutOfScope : KindCheckError

def checkTyVar
    : (Φ : KindCtx) → (k : Kind) → Nat → Except KindCheckError (InKindCtx Φ k)
| .empty, _, _ => .error .tyVarOutOfScope
| .extend _ .TyKind, .TyKind, 0 => .ok .here
| .extend Φ _, k, .succ n => do
    let x ← checkTyVar Φ k n
    .ok (.there x)

def checkKinds (Φ : KindCtx) (k : Kind)
    : RawTy → Except KindCheckError (Ty Φ k)
| .NatTy => .ok .NatTy
| .BoolTy => .ok .BoolTy
| .FunTy a b => do
    let erasedA ← checkKinds Φ k a
    let erasedB ← checkKinds Φ k b
    .ok (.FunTy erasedA erasedB)
| .TyVar x => do
    let erasedX ← checkTyVar Φ k x
    .ok (.TyVar erasedX)
| .Forall k' a => do
    let erasedA ← checkKinds (.extend Φ k') k a
    .ok (.Forall k' erasedA)

-- Some inversion lemmas --
section checkKinds_inversion
theorem checkKindsNatTy : ∀ {Φ k} {a}, checkKinds Φ k a = .ok .NatTy → a = .NatTy := by
  intros Φ k a h
  cases a <;> simp [checkKinds, bind, Except.bind] at h
  all_goals (repeat (split at h <;> simp_all))
  rfl

theorem checkKindsBoolTy : ∀ {Φ k} {a}, checkKinds Φ k a = .ok .BoolTy → a = .BoolTy := by
  intros Φ k a h
  cases a <;> simp [checkKinds, bind, Except.bind] at h
  all_goals (repeat (split at h <;> simp_all))
  rfl

theorem checkKindsFunTy : ∀ {Φ k} {t a b},
    checkKinds Φ k t = .ok (.FunTy a b) →
    ∃ a', ∃ b', (checkKinds Φ k a' = .ok a ∧ checkKinds Φ k b' = .ok b ∧ t = .FunTy a' b') := by
  intros Φ k t a b h
  cases t <;> simp_all [checkKinds, bind, Except.bind]
  all_goals repeat (split at h <;> simp_all)
  grind

theorem checkTyVar_erase {Φ k n x} (h : checkTyVar Φ k n = .ok x) : n = eraseTyVarKinds x := by
  induction Φ generalizing n with
  | empty => simp [checkTyVar] at h
  | extend Φ k' ih =>
    cases n <;> simp [checkTyVar, bind, Except.bind] at h
    case zero => subst h; rfl
    case succ n =>
      split at h <;> simp_all
      rw [← h]
      simp!
      apply ih
      grind

theorem checkKindsTyVar : ∀ {Φ k} {t x},
    checkKinds Φ k t = .ok (.TyVar x) →
    ∃ n, (eraseTyVarKinds x = n ∧ t = .TyVar n) := by
  intros Φ k t x h
  cases t <;> simp_all [checkKinds, bind, Except.bind]
  all_goals repeat (split at h <;> simp_all)
  case FunTy => grind
  case h_2 => exact checkTyVar_erase ‹_›

theorem checkKindsForall : ∀ {Φ k} {t k' a},
    checkKinds Φ k t = .ok (.Forall k a) →
    ∃ a', (checkKinds (Φ.extend k') k a' = .ok a ∧ t = .Forall k' a') := sorry
end checkKinds_inversion

-- `eraseKinds` is a left inverse of `checkKinds`
theorem checkErase {Φ k} : ∀ {a aWF},
    checkKinds Φ k a = .ok aWF →
    eraseKinds aWF = a := by
  intros a0 aWF0 eq
  induction aWF0 generalizing a0 with
  | NatTy =>
      rw [checkKindsNatTy eq]
      simp!
  | BoolTy =>
      rw [checkKindsBoolTy eq]
      simp!
  | FunTy a b aIH bIH =>
      obtain ⟨a', b', p, q, r⟩ := checkKindsFunTy eq
      simp! [aIH p, bIH q]
      grind
  | TyVar x =>
      obtain ⟨n, p, q⟩ := checkKindsTyVar eq
      simp! [p, q]
  | Forall x b =>
      obtain ⟨a', p, q⟩ := checkKindsForall eq
      simp! [p, q]
      grind

def TyRenaming Φ Φ' :=
  forall {k},
  InKindCtx Φ k →
  InKindCtx Φ' k

def TySubst Φ Φ' :=
  forall {k},
  InKindCtx Φ k →
  Ty Φ' k

def liftTyRenaming {Φ Φ' k} :
    TyRenaming Φ Φ' →
    TyRenaming (.extend Φ k) (.extend Φ' k)
| _, _k', .here => .here
| ρ, _k', .there x => .there (ρ x)

def renameTy {Φ Φ' k} :
    TyRenaming Φ Φ' →
    Ty Φ k →
    Ty Φ' k
| _, .NatTy => .NatTy
| _, .BoolTy => .BoolTy
| ρ, .FunTy a b => .FunTy (renameTy ρ a) (renameTy ρ b)
| ρ, .TyVar x => .TyVar (ρ x)
| ρ, .Forall k b => .Forall k (renameTy (liftTyRenaming ρ) b)

def liftTySubst {Φ Φ' k} :
    TySubst Φ Φ' →
    TySubst (.extend Φ k) (.extend Φ' k)
| _, _k', .here => .TyVar .here
| σ, _k', .there x => renameTy .there (σ x)

def substTy {Φ Φ' k} (σ : TySubst Φ Φ') :
    Ty Φ k →
    Ty Φ' k
| .NatTy => .NatTy
| .BoolTy => .BoolTy
| .FunTy a b => .FunTy (substTy σ a) (substTy σ b)
| .TyVar x => σ x
| .Forall k b => .Forall k (substTy (liftTySubst σ) b)

def substTy1 {Φ k k'} :
    Ty (.extend Φ k) k' →
    Ty Φ k →
    Ty Φ k' :=
  fun n m =>
  let σ {k2} : InKindCtx (.extend Φ k) k2 → Ty Φ k2
      | .here => m
      | .there x => .TyVar x
  substTy σ n
