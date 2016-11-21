{-# OPTIONS --without-K --rewriting #-}

open import Agda.Primitive

infix -10 _↦_

postulate _↦_ : ∀ {a} {A : Set a} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}

infix 1 _≡_
infix 2 _≡[_]_

infix 4 ⟦_⟧Set
infix 5 ⟦_⟧

_≡_ : ∀ {a} {A : Set a} → A → A → Set a
⟦_⟧Set : ∀ {a} {A : Set a} (x : A) → x ≡ x

postulate
  _≡[_]_ : ∀ {a} {A B : Set a} → A → A ≡ B → B → Set a
  ⟦_⟧ : ∀ {a} {A : Set a} (x : A) → x ≡[ ⟦ A ⟧Set ] x

_≡_ {a} {A} x₀ x₁ = x₀ ≡[ ⟦ A ⟧Set ] x₁
⟦ A ⟧Set = ⟦ A ⟧

postulate
  Π≡ : ∀ {a b} {A₀ A₁ : Set a} {B₀ : A₀ → Set b} {B₁ : A₁ → Set b}
     → (A : A₀ ≡ A₁) (B : {x₀ : A₀} {x₁ : A₁} (x : x₀ ≡[ A ] x₁) → B₀ x₀ ≡ B₁ x₁)
     → ((x : A₀) → B₀ x) ≡ ((x : A₁) → B₁ x)
  ≡-fun : ∀ {a b} {A₀ A₁ : Set a} {B₀ : A₀ → Set b} {B₁ : A₁ → Set b}
        → (A : A₀ ≡ A₁) (B : {x₀ : A₀} {x₁ : A₁} (x : x₀ ≡[ A ] x₁) → B₀ x₀ ≡ B₁ x₁)
        → (f₀ : (x : A₀) → B₀ x) (f₁ : (x : A₁) → B₁ x)
        → f₀ ≡[ Π≡ A B ] f₁ ↦ ({x₀ : A₀} {x₁ : A₁} (x : x₀ ≡[ A ] x₁) → f₀ x₀ ≡[ B x ] f₁ x₁)

{-# REWRITE ≡-fun #-}

→≡ : ∀ {a b} {A₀ A₁ : Set a} {B₀ B₁ : Set b}
     → (A : A₀ ≡ A₁) (B : B₀ ≡ B₁) → (A₀ → B₀) ≡ (A₁ → B₁)
→≡ A B = Π≡ A (λ _ → B)

postulate
  ⟦→⟧ : ∀ {a b} {A : Set a} {B : Set b}
      → ⟦ (A → B) ⟧ ↦ →≡ ⟦ A ⟧ ⟦ B ⟧

{-# REWRITE ⟦→⟧ #-}

postulate
  ⟦⟧-const : ∀ {a b} {A : Set a} {B : Set b}
           → (b : B) {x₀ x₁ : A} (x : x₀ ≡ x₁)
           → ⟦ (λ (_ : A) → b) ⟧ x ↦ ⟦ b ⟧
  ⟦Π⟧ : ∀ {a b} {A : Set a} {B : A → Set b}
      → ⟦ ((x : A) → B x) ⟧ ↦ Π≡ ⟦ A ⟧ ⟦ B ⟧

{-# REWRITE ⟦⟧-const #-}
{-# REWRITE ⟦Π⟧ #-}

postulate
  ⟦⟧⟦⟧′ : ∀ {a b} {A : Set a} {B : Set b}
        → (f : A → B) (x : A) → ⟦ f ⟧ ⟦ x ⟧ ↦ ⟦ f x ⟧

{-# REWRITE ⟦⟧⟦⟧′ #-}

postulate
  ⟦⟧⟦⟧ : ∀ {a b} {A : Set a} {B : A → Set b}
       → (f : (x : A) → B x) (x : A)
       → ⟦ f ⟧ ⟦ x ⟧ ↦ ⟦ f x ⟧

{-# REWRITE ⟦⟧⟦⟧ #-}

postulate
  coe    : ∀ {a} {A₀ A₁ : Set a} (A : A₀ ≡ A₁) → A₀ → A₁
  coe′   : ∀ {a} {A₀ A₁ : Set a} (A : A₀ ≡ A₁) → A₁ → A₀
  coe⟦⟧  : ∀ {a} (A : Set a) (x : A) → coe  ⟦ A ⟧ x ↦ x
  coe′⟦⟧ : ∀ {a} (A : Set a) (x : A) → coe′ ⟦ A ⟧ x ↦ x

{-# REWRITE coe⟦⟧ #-}
{-# REWRITE coe′⟦⟧ #-}

postulate
  coh    : ∀ {a} {A₀ A₁ : Set a} (A : A₀ ≡ A₁) (x : A₀) → x ≡[ A ] coe A x
  coh′   : ∀ {a} {A₀ A₁ : Set a} (A : A₀ ≡ A₁) (x : A₁) → coe′ A x ≡[ A ] x
  coh⟦⟧  : ∀ {a} (A : Set a) (x : A) → coh  ⟦ A ⟧ x ↦ ⟦ x ⟧
  coh′⟦⟧ : ∀ {a} (A : Set a) (x : A) → coh′ ⟦ A ⟧ x ↦ ⟦ x ⟧

{-# REWRITE coh⟦⟧  #-}
{-# REWRITE coh′⟦⟧ #-}

postulate
  coe-Π≡ : ∀ {a b} {A₀ A₁ : Set a} {B₀ : A₀ → Set b} {B₁ : A₁ → Set b}
         → (A : A₀ ≡ A₁) (B : {x₀ : A₀} {x₁ : A₁} (x : x₀ ≡[ A ] x₁) → B₀ x₀ ≡ B₁ x₁)
         → (f : (x : A₀) → B₀ x)
         → coe (Π≡ A B) f ↦ (λ x → coe (B (coh′ A x)) (f (coe′ A x)))
  coe′-Π≡ : ∀ {a b} {A₀ A₁ : Set a} {B₀ : A₀ → Set b} {B₁ : A₁ → Set b}
          → (A : A₀ ≡ A₁) (B : {x₀ : A₀} {x₁ : A₁} (x : x₀ ≡[ A ] x₁) → B₀ x₀ ≡ B₁ x₁)
          → (f : (x : A₁) → B₁ x)
          → coe′ (Π≡ A B) f ↦ (λ x → coe′ (B (coh A x)) (f (coe A x)))

{-# REWRITE coe-Π≡  #-}
{-# REWRITE coe′-Π≡ #-}

ap : ∀ {a b} {A : Set a} {B : Set b} (f : A → B)
   → {x y : A} (e : x ≡ y) → f x ≡ f y
ap f e = ⟦ f ⟧ e

transport : ∀ {a b} {A : Set a} (B : A → Set b)
          → {x y : A} (e : x ≡ y) → B x → B y
transport B e = coe (⟦ B ⟧ e)

refl : ∀ {a} {A : Set a} {x : A} → x ≡ x
refl {x = x} = ⟦ x ⟧

sym : ∀ {a} (A : Set a) {x y : A} → x ≡ y → y ≡ x
sym A {x = x} p = transport (λ y → y ≡ x) p ⟦ x ⟧

trans : ∀ {a} (A : Set a) {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans A {x = x} p q = transport (λ y → x ≡ y) q p

postulate -- Needed for J (?)
  ⟦λΠ⟧   : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
         → {x₀ x₁ : A} (x : x₀ ≡ x₁)
         → ⟦ (λ x → (y : B x) → C x) ⟧ x ↦ Π≡ (⟦ B ⟧ x) (λ y → ⟦ C ⟧ x)
  coe-≡  : ∀ {a} {A : Set a} {x y : A} (e : x ≡ y)
         → coe (⟦ (λ y → x ≡ y) ⟧ e) ⟦ x ⟧ ↦ e
  coe′-≡ : ∀ {a} {A : Set a} {x y : A} (e : x ≡ y)
         → coe′ (⟦ (λ x → x ≡ y) ⟧ e) ⟦ y ⟧ ↦ e

{-# REWRITE ⟦λΠ⟧ #-}
{-# REWRITE coe-≡  #-}
{-# REWRITE coe′-≡ #-}

record Σ {a} {b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

J′ : ∀ {a b} {A : Set a} {x : A} (B : Σ A (λ y → x ≡ y) → Set b)
  → B (x , ⟦ x ⟧) → (u : Σ A (λ y → x ≡ y)) → B u
J′ {A = A} {x = x} B b (y , e) = transport B (⟦ _,_ ⟧ e (coh (⟦ (λ y → x ≡ y) ⟧ e) ⟦ x ⟧)) b

J : ∀ {a b} {A : Set a} {x : A} (B : {y : A} → x ≡ y → Set b)
  → B ⟦ x ⟧ → {y : A} (e : x ≡ y) → B e
J B b e = J′ (λ { (y , e) → B {y} e }) b (_ , e)


apd : ∀ {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x)
   → {x y : A} (e : x ≡ y) → f x ≡[ ⟦ B ⟧ e ] f y
apd f e = ⟦ f ⟧ e


transportd : ∀ {a b} {A₀ A₁ : Set a} {A : A₀ ≡ A₁}
           → {B₀ : A₀ → Set b} {B₁ : A₁ → Set b}
           → (B : B₀ ≡[ →≡ A ⟦ Set b ⟧ ] B₁)
           → {x₀ : A₀} {x₁ : A₁} (x : x₀ ≡[ A ] x₁) → B₀ x₀ → B₁ x₁
transportd B x = coe (B x)

Jd : ∀ {a p} {A₀ : Set a} {x₀ : A₀}
   → (P : {A₁ : Set a} (A : A₀ ≡ A₁) {x₁ : A₁} (x : x₀ ≡[ A ] x₁) → Set p)
   → (p : P ⟦ A₀ ⟧ ⟦ x₀ ⟧)
   → {A₁ : Set a} {x₁ : A₁} (A : A₀ ≡ A₁) (x : x₀ ≡[ A ] x₁) → P A x
Jd {A₀ = A₀} {x₀ = x₀} P p A x = J (λ {A₁} A → {x₁ : A₁} (x₂ : x₀ ≡[ A ] x₁) → P A x₂)
                                   (λ {x₁} → J (λ {x₁} x → P ⟦ A₀ ⟧ x) p {x₁}) A x

symd  : ∀ {a} {A₀ A₁ : Set a} (A : A₀ ≡ A₁)
     → {x₀ : A₀} {x₁ : A₁} → x₀ ≡[ A ] x₁ → x₁ ≡[ sym (Set a) A ] x₀
symd {a} {A₀} A {x₀} = Jd (λ A {x₁} x → x₁ ≡[ sym (Set a) A ] x₀) ⟦ x₀ ⟧ A

transd : ∀ {a} {A₀ A₁ A₂ : Set a} (A : A₀ ≡ A₁) (A′ : A₁ ≡ A₂)
       → {x₀ : A₀} {x₁ : A₁} {x₂ : A₂}
       → x₀ ≡[ A ] x₁ → x₁ ≡[ A′ ] x₂ → x₀ ≡[ trans (Set a) A A′ ] x₂
transd {a} {A₀} {A₁} A A′ {x₀} x x′ =
  Jd (λ {A₁} A {x₁} x → {A₂ : Set a} (A′ : A₁ ≡ A₂) {x₂ : A₂}
                        → x₁ ≡[ A′ ] x₂ → x₀ ≡[ trans (Set a) A A′ ] x₂)
     (λ A′ x′ → Jd (λ A′ {x₂} x′ → x₀ ≡[ (trans (Set a) ⟦ A₀ ⟧ A′) ] x₂)
                   ⟦ x₀ ⟧ A′ x′)
     A x A′ x′

postulate
  coh-Π≡ : ∀ {a b} {A₀ A₁ : Set a} {B₀ : A₀ → Set b} {B₁ : A₁ → Set b}
         → (A : A₀ ≡ A₁) (B : B₀ ≡[ →≡ A ⟦ Set b ⟧ ] B₁)
         → (f : (x : A₀) → B₀ x) {x₀ : A₀} {x₁ : A₁} (x : x₀ ≡[ A ] x₁)
         → coh (Π≡ A B) f x ↦ {!!}

  coh′-Π≡ : ∀ {a b} {A₀ A₁ : Set a} {B₀ : A₀ → Set b} {B₁ : A₁ → Set b}
          → (A : A₀ ≡ A₁) (B : {x₀ : A₀} {x₁ : A₁} (x : x₀ ≡[ A ] x₁) → B₀ x₀ ≡ B₁ x₁)
          → (f : (x : A₁) → B₁ x) {x₀ : A₀} {x₁ : A₁} (x : x₀ ≡[ A ] x₁)
          → coh′ (Π≡ A B) f x ↦ {!!}


funextd : ∀ {a b} {A : Set a} {B : A → Set b}
        → {f g : (x : A) → B x}
        → ({x₀ x₁ : A} (x : x₀ ≡ x₁) → f x₀ ≡[ ⟦ B ⟧ x ] g x₁) → f ≡ g
funextd p x = p x

funext : ∀ {a b} {A : Set a} {B : A → Set b}
       → {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g
funext {B = B} {f} {g} p {x₀} = J (λ {x₁} x → f x₀ ≡[ ⟦ B ⟧ x ] g x₁) (p x₀)
