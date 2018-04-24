module Delay where

open import Level public
  using (Level) renaming (zero to lzero; suc to lsuc)

open import Size public

open import Category.Monad public
  using (RawMonad; module RawMonad)

open import Relation.Binary public
  using (Setoid; module Setoid)

import Relation.Binary.PreorderReasoning
module Pre = Relation.Binary.PreorderReasoning

open import Function public
  using (_∘_; case_of_)

open import Data.Product public
  using (∃; _×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

mutual
  data Delay (i : Size) (A : Set) : Set where
    now    :  A           → Delay i A
    later  :  ∞Delay i A  → Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    field
      force : {j : Size< i} → Delay j A

open ∞Delay public

never                  :  ∀{i A} → ∞Delay i A
force (never {i}) {j}  =  later (never {j})

module Bind where
  mutual
    _>>=_              :  ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
    now    a   >>=  f  =  f a
    later  a∞  >>=  f  =  later (a∞ ∞>>= f)

    _∞>>=_             :  ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    force (a∞ ∞>>= f)  =  force a∞ >>= f

delayMonad : ∀ {i} → RawMonad (Delay i)
delayMonad {i} = record
  { return  =  now
  ; _>>=_   =  _>>=_ {i}
  } where open Bind

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i})
                           public renaming (_⊛_ to _<*>_)

open Bind public using (_∞>>=_)

_∞<$>_ : ∀ {i A B} (f : A → B) (∞a : ∞Delay i A) → ∞Delay i B
f ∞<$> ∞a = ∞a ∞>>= λ a → return (f a)
-- force (f ∞<$> ∞a) = f <$> force ∞a

_=<<2_,_ : ∀ {i A B C} → (A → B → Delay i C) → Delay i A → Delay i B → Delay i C
f =<<2 x , y = x >>= λ a → y >>= λ b → f a b

--------------------------------------------------------------------------------
-- Bisimilarity
--------------------------------------------------------------------------------

mutual
  data _∼_ {i : Size} {A : Set} : (a? b? : Delay ∞ A) → Set where
    ∼now    :  ∀ a                              →  now a     ∼ now a
    ∼later  :  ∀ {a∞ b∞} (eq : a∞ ∞∼⟨ i ⟩∼ b∞)  →  later a∞  ∼ later b∞

  _∼⟨_⟩∼_ = λ {A} a? i b? → _∼_ {i}{A} a? b?

  record _∞∼⟨_⟩∼_ {A} (a∞ : ∞Delay ∞ A) i (b∞ : ∞Delay ∞ A) : Set where
    coinductive
    field
      ∼force : {j : Size< i} → force a∞ ∼⟨ j ⟩∼ force b∞

  _∞∼_ = λ {i} {A} a∞ b∞ → _∞∼⟨_⟩∼_ {A} a∞ i b∞

open _∞∼⟨_⟩∼_ public

∼never : ∀{i A} → (never {A = A}) ∞∼⟨ i ⟩∼ never
∼force ∼never = ∼later ∼never

∼refl    :  ∀{i A} (a?  : Delay ∞ A)   →  a? ∼⟨ i ⟩∼ a?
∞∼refl   :  ∀{i A} (a∞  : ∞Delay ∞ A)  →  a∞ ∞∼⟨ i ⟩∼ a∞
∼sym     :  ∀{i A}{a?  b?  : Delay ∞ A }  →  a? ∼⟨ i ⟩∼ b?   →  b? ∼⟨ i ⟩∼ a?
∞∼sym    :  ∀{i A}{a∞  b∞  : ∞Delay ∞ A}  →  a∞ ∞∼⟨ i ⟩∼ b∞  →  b∞ ∞∼⟨ i ⟩∼ a∞
∼trans   :  ∀{i A}{a? b? c? : Delay ∞ A} → a? ∼⟨ i ⟩∼ b? →  b? ∼⟨ i ⟩∼ c? → a? ∼⟨ i ⟩∼ c?
∞∼trans  :  ∀{i A}{a∞ b∞ c∞ : ∞Delay ∞ A} → a∞ ∞∼⟨ i ⟩∼ b∞ →  b∞ ∞∼⟨ i ⟩∼ c∞ → a∞ ∞∼⟨ i ⟩∼ c∞

∼refl (now x)   = ∼now x
∼refl (later x) = ∼later (∞∼refl x)
∼force (∞∼refl a∞) = ∼refl (force a∞)

∼sym (∼now eq)   = ∼now eq
∼sym (∼later eq) = ∼later (∞∼sym eq)
∼force (∞∼sym eq) = ∼sym (∼force eq)

∼trans (∼now a) (∼now .a) = ∼now a
∼trans (∼later eq₁) (∼later eq₂) = ∼later (∞∼trans eq₁ eq₂)
∼force (∞∼trans eq₁ eq₂) = ∼trans (∼force eq₁) (∼force eq₂)

∼setoid : (i : Size) (A : Set) → Setoid lzero lzero
∼setoid i A = record
  { Carrier       = Delay ∞ A
  ; _≈_           = _∼_ {i}
  ; isEquivalence =
    record
    { refl  = λ {a∞} → ∼refl a∞
    ; sym   = ∼sym
    ; trans = ∼trans
    }
  }

∞∼setoid : (i : Size) (A : Set) → Setoid lzero lzero
∞∼setoid i A = record
  { Carrier = ∞Delay ∞ A
  ; _≈_ = _∞∼_ {i} {A}
  ; isEquivalence =
      record
      { refl  = λ {a?} → ∞∼refl a?
      ; sym   = ∞∼sym
      ; trans = ∞∼trans
      }
  }

module ∼-Reasoning {i : Size} {A : Set} where
  open Pre (Setoid.preorder (∼setoid i A)) public
    renaming (_≈⟨⟩_ to _≡⟨⟩_; _≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _∼⟨_⟩_; begin_ to proof_)

module ∞∼-Reasoning {i : Size} {A : Set} where
  open Pre (Setoid.preorder (∞∼setoid i A)) public
    renaming (_≈⟨⟩_ to _≡⟨⟩_; _≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _∞∼⟨_⟩_; begin_ to proof_)


mutual
  bind-assoc               :  ∀{i A B C} (m : Delay ∞ A)
                              {k : A → Delay ∞ B} {l : B → Delay ∞ C} →
                              ((m >>= k) >>= l) ∼⟨ i ⟩∼ (m >>= λ a → (k a >>= l))
  bind-assoc (now a)       = ∼refl _
  bind-assoc (later a∞)    = ∼later (∞bind-assoc a∞)

  ∞bind-assoc              :  ∀{i A B C} (a∞ : ∞Delay ∞ A)
                              {k : A → Delay ∞ B} {l : B → Delay ∞ C} →
                              ((a∞ ∞>>= k) ∞>>= l) ∞∼⟨ i ⟩∼ (a∞ ∞>>= λ a → (k a >>= l))
  ∼force (∞bind-assoc a∞)  = bind-assoc (force a∞)

bind-cong-l   :  ∀{i A B}{a? b? : Delay ∞ A} →  a? ∼⟨ i ⟩∼ b? →
                 (k : A → Delay ∞ B) → (a? >>= k) ∼⟨ i ⟩∼ (b? >>= k)

∞bind-cong-l  :  ∀{i A B}{a∞ b∞ : ∞Delay ∞ A} → a∞ ∞∼⟨ i ⟩∼ b∞ →
                 (k : A → Delay ∞ B) → (a∞ ∞>>= k) ∞∼⟨ i ⟩∼ (b∞ ∞>>= k)

bind-cong-r   :  ∀{i A B}(a? : Delay ∞ A){k l : A → Delay ∞ B} →
                 (∀ a → (k a) ∼⟨ i ⟩∼ (l a)) → (a? >>= k) ∼⟨ i ⟩∼ (a? >>= l)

∞bind-cong-r  :  ∀{i A B}(a∞ : ∞Delay ∞ A){k l : A → Delay ∞ B} →
                 (∀ a → (k a) ∼⟨ i ⟩∼ (l a)) → (a∞ ∞>>= k) ∞∼⟨ i ⟩∼ (a∞ ∞>>= l)

bind-cong-l (∼now a) k    = ∼refl _
bind-cong-l (∼later eq) k = ∼later (∞bind-cong-l eq k)

∼force (∞bind-cong-l eq k) = bind-cong-l (∼force eq) k

bind-cong-r (now x) k   = k x
bind-cong-r (later x) k = ∼later (∞bind-cong-r x k)

∼force (∞bind-cong-r a∞ h) = bind-cong-r (force a∞) h

map-compose     :  ∀{i A B C} (a? : Delay ∞ A) {f : A → B} {g : B → C} →
                   (g <$> (f <$> a?)) ∼⟨ i ⟩∼ ((g ∘ f) <$> a?)
map-compose a?  =  bind-assoc a?

map-cong        :  ∀{i A B}{a? b? : Delay ∞ A} (f : A → B) →
                   a? ∼⟨ i ⟩∼ b? → (f <$> a?) ∼⟨ i ⟩∼ (f <$> b?)
map-cong f eq   =  bind-cong-l eq (now ∘ f)

--------------------------------------------------------------------------------
-- Convergence
--------------------------------------------------------------------------------

data _⇓_ {A : Set} : (a? : Delay ∞ A) (a : A) → Set where
  now⇓    :  ∀{a}                                   → now a ⇓ a
  later⇓  :  ∀{a} {a∞ : ∞Delay ∞ A} → force a∞ ⇓ a  → later a∞ ⇓ a

_⇓   :  {A : Set} (x : Delay ∞ A) → Set
x ⇓  =  ∃ λ a → x ⇓ a

map⇓     :  ∀{A B}{a : A}{a? : Delay ∞ A}(f : A → B) → a? ⇓ a → (f <$> a?) ⇓ f a

subst∼⇓  :  ∀{A}{a? a?′ : Delay ∞ A}{a : A} → a? ⇓ a → a? ∼ a?′ → a?′ ⇓ a

bind⇓    :  ∀{A B}(f : A → Delay ∞ B){?a : Delay ∞ A}{a : A}{b : B} →
            ?a ⇓ a → f a ⇓ b → (?a >>= f) ⇓ b

map⇓ f now⇓        = now⇓
map⇓ f (later⇓ a⇓) = later⇓ (map⇓ f a⇓)

subst∼⇓ now⇓ (∼now a)  = now⇓
subst∼⇓ (later⇓ a⇓) (∼later eq) = later⇓ (subst∼⇓ a⇓ (∼force eq))

bind⇓ f now⇓ fa⇓        = fa⇓
bind⇓ f (later⇓ a⇓) fa⇓ = later⇓ (bind⇓ f a⇓ fa⇓)
