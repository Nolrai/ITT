universes u v

import Order

class PreCategory (α : Type u) where
  (Hom : α → α → Type v)

open PreCategory

infixr:30 " ⟶ " => Hom

class CategoryRaw (Obj : Type u) extends PreCategory Obj where
  (id' : {a : Obj} → Hom a a)
  (comp : {α β γ : Obj} → (β ⟶ γ) → (α ⟶ β)  → (α ⟶ γ))

open CategoryRaw
infixr:70 " ∘ " => comp
infixr:70 " ; " => flip comp

class Category (Obj : Type u) extends CategoryRaw Obj where
  (left_unit : {α β : Obj} → (f : α ⟶ β) → id' ∘ f = f)
  (right_unit : {α β : Obj} → (f : α ⟶ β) → f ∘ id' = f)
  (assoc : {α β γ δ : Obj} → 
    (f : α ⟶ β) → (g : β ⟶ γ) → (h : γ ⟶ δ) →
    (f ; g) ; h = f ; (g ; h))

class HasTerminal (Obj : Type u) extends Category Obj where
  (terminal : Obj)
  (bang : {α : Obj} → α ⟶ terminal)
  (bang_unique : ∀ {f : α ⟶ terminal}, f = bang)

class CartesianRaw (Obj : Type u) extends Category Obj where
  (cprod : Obj → Obj → Obj)
  (pair : {α β γ : Obj} → (γ ⟶ α) → (γ ⟶ β) -> γ ⟶ cprod α β)
  (π₁ : {α β : Obj} → cprod α β ⟶ α )
  (π₂ : {α β : Obj} → cprod α β ⟶ β )

open CartesianRaw

infixr " × " => CartesianRaw.cprod
infixr " >< " => CartesianRaw.pair
infixr " .×. " => λ f₁ f₂ => (π₁;f₁) >< (π₂;f₂)

def projects_left {Obj} [CartesianRaw Obj] (α β γ : Obj) 
  (f : (γ ⟶ α) → (γ ⟶ β) -> γ ⟶ (α × β)) := 
  ∀ (f₁ : γ ⟶ α) (f₂ : γ ⟶ β), 
    (f f₁ f₂ : γ ⟶ (α × β)) ; π₁ = f₁

def projects_right {Obj} [CartesianRaw Obj] (α β γ : Obj) 
  (f : (γ ⟶ α) → (γ ⟶ β) -> γ ⟶ (α × β)) := 
  ∀ (f₁ : γ ⟶ α) (f₂ : γ ⟶ β),
  (f f₁ f₂ : γ ⟶ (α × β)) ; π₂ = f₂

class Cartesian (Obj : Type u) extends CartesianRaw Obj where
  (cprod_f_projects_left {α β γ : Obj} : projects_left α β γ pair)
  (cprod_f_projects_Right {α β γ : Obj} : projects_right α β γ pair)
  (cprod_f_unique {α β γ : Obj} (f : γ ⟶ α → γ ⟶ β → γ ⟶ α × β) : 
    projects_left α β γ f ∧ projects_right α β γ f → f = pair)

class CartesianClosedRaw (Obj : Type u) extends Cartesian Obj where
  (exp : Obj → Obj → Obj)
  (eval {α β} : Hom (exp α β × β) α)
  (curry {α β γ} : Hom (α × β) γ → Hom α (exp γ β))

infix " ⇒ " => flip CartesianClosedRaw.exp

open CartesianClosedRaw

class CartesianClosed (Obj : Type u) extends CartesianClosedRaw Obj where
  (eval_of_curry {α β γ : Obj} {g : (α × β) ⟶ γ} : ((curry g .×. id') ; eval : (α × β) ⟶ γ) = g)
  (curry_of_eval {α β γ : Obj} {h : α ⟶ (β ⇒ γ)} : curry ((h .×. id') ; eval) = h)

class CoCartesianRaw (Obj : Type u) extends Category Obj where
  (csum : Obj → Obj → Obj)
  (cases {α β γ : Obj} : α ⟶ γ → β ⟶ γ → (csum α β ⟶ γ))
  (i₁ {α β : Obj} : α ⟶ csum α β)
  (i₂ {α β : Obj} : β ⟶ csum α β)

open CoCartesianRaw

infix " ∔ " => CoCartesianRaw.csum
infixr " .|. " => CoCartesianRaw.cases
infixr " .+. " => λ f₁ f₂ => (f₁;i₁) .|. (f₂;i₂)

def injects_left {Obj} [CoCartesianRaw Obj] (α β γ : Obj) 
  (f : (α ⟶ γ) → (β ⟶ γ) -> (α ∔ β) ⟶ γ) := 
  ∀ (f₁ : α ⟶ γ) (f₂ : β ⟶ γ), 
    i₁ ; (f f₁ f₂ : (α ∔ β) ⟶ γ) = f₁

def injects_right {Obj} [CoCartesianRaw Obj] (α β γ : Obj) 
  (f : (α ⟶ γ) → (β ⟶ γ) -> (α ∔ β) ⟶ γ) := 
  ∀ (f₁ : α ⟶ γ) (f₂ : β ⟶ γ), 
    i₂ ; (f f₁ f₂ : (α ∔ β) ⟶ γ) = f₂

class CoCarteasian (Obj : Type u) extends CoCartesianRaw Obj where
  (csum_f_projects_left {α β γ : Obj} : injects_left α β γ cases)
  (csum_f_projects_Right {α β γ : Obj} : injects_right α β γ cases)
  (csum_f_unique {α β γ : Obj} (f : α ⟶ γ → β ⟶ γ → (α ∔ β) ⟶ γ) : 
    injects_left α β γ f ∧ injects_right α β γ f → f = cases)

