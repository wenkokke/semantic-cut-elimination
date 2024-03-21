------------------------------------------------------------------------
-- The Agda standard library
--
-- Ordered algebraic structures (not packed up with sets, orders,
-- operations, etc.)
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Algebra.Ordered`.

{-# OPTIONS --postfix-projections --without-K --safe #-}

open import Relation.Binary.Core using (Rel; _⇒_)

module Algebra.Ordered.Structures
  {a ℓ₁ ℓ₂} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ₁)       -- The underlying equality relation
  (_≲_ : Rel A ℓ₂)       -- The underlying order relation
  where

open import Algebra.Core
open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
open import Algebra.Ordered.Definitions _≲_
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (flip; _$_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.Consequences using (mono₂⇒cong₂)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

------------------------------------------------------------------------
-- Preordered structures

-- Preordered magmas (promagmas)

record IsPromagma (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreorder  : IsPreorder _≈_ _≲_
    ∙-cong      : Congruent₂ ∙
    mono        : Monotonic₂ _≲_ _≲_ _≲_ ∙

  open IsPreorder isPreorder public

  monoˡ : ∀ {x} → Monotonic₁ _≲_ _≲_ (flip ∙ x)
  monoˡ y≈z = mono y≈z refl

  monoʳ : ∀ {x} → Monotonic₁ _≲_ _≲_ (∙ x)
  monoʳ y≈z = mono refl y≈z

  isMagma : IsMagma ∙
  isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∙-cong }

  open IsMagma isMagma public using (setoid; ∙-congˡ; ∙-congʳ)

-- Preordered semigroups (prosemigroups)

record IsProsemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPromagma  : IsPromagma ∙
    assoc       : Associative ∙

  open IsPromagma isPromagma public

  isSemigroup : IsSemigroup ∙
  isSemigroup = record { isMagma = isMagma ; assoc = assoc }

-- Preordered monoids (promonoids)

record IsPromonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isProsemigroup : IsProsemigroup ∙
    identity       : Identity ε ∙

  open IsProsemigroup isProsemigroup public

  isMonoid : IsMonoid ∙ ε
  isMonoid = record { isSemigroup = isSemigroup ; identity = identity }

  open IsMonoid isMonoid public using (identityˡ; identityʳ)

-- Preordered commutative monoids (commutative promonoids)

record IsCommutativePromonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPromonoid : IsPromonoid ∙ ε
    comm        : Commutative ∙

  open IsPromonoid isPromonoid public

  isCommutativeMonoid : IsCommutativeMonoid ∙ ε
  isCommutativeMonoid = record { isMonoid = isMonoid ; comm = comm }

  open IsCommutativeMonoid isCommutativeMonoid public
    using (isCommutativeSemigroup)

-- Preordered semirings (prosemirings)

record IsProsemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    +-isCommutativePromonoid : IsCommutativePromonoid + 0#
    *-cong                   : Congruent₂ *
    *-mono                   : Monotonic₂ _≲_ _≲_ _≲_ *
    *-assoc                  : Associative *
    *-identity               : Identity 1# *
    distrib                  : * DistributesOver +
    zero                     : Zero 0# *

  open IsCommutativePromonoid +-isCommutativePromonoid public
    renaming
    ( assoc                  to +-assoc
    ; ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; mono                   to +-mono
    ; monoˡ                  to +-monoˡ
    ; monoʳ                  to +-monoʳ
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; comm                   to +-comm
    ; isMagma                to +-isMagma
    ; isSemigroup            to +-isSemigroup
    ; isMonoid               to +-isMonoid
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    ; isCommutativeMonoid    to +-isCommutativeMonoid
    )

  *-isPromonoid : IsPromonoid * 1#
  *-isPromonoid = record
    { isProsemigroup = record
      { isPromagma   = record
        { isPreorder = isPreorder
        ; ∙-cong     = *-cong
        ; mono       = *-mono
        }
      ; assoc        = *-assoc
      }
    ; identity       = *-identity
    }

  open IsPromonoid *-isPromonoid public
    using ()
    renaming
    ( ∙-congˡ     to *-congˡ
    ; ∙-congʳ     to *-congʳ
    ; monoˡ       to *-monoˡ
    ; monoʳ       to *-monoʳ
    ; identityˡ   to *-identityˡ
    ; identityʳ   to *-identityʳ
    ; isMagma     to *-isMagma
    ; isSemigroup to *-isSemigroup
    ; isMonoid    to *-isMonoid
    )

  isSemiring : IsSemiring + * 0# 1#
  isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid           = +-isCommutativeMonoid
      ; *-cong                          = *-cong
      ; *-assoc                         = *-assoc
      ; *-identity                      = *-identity
      ; distrib                         = distrib
      }
    ; zero                              = zero
    }

  open IsSemiring isSemiring public using (distribˡ; distribʳ; zeroˡ; zeroʳ)

------------------------------------------------------------------------
-- Partially ordered structures

-- Partially ordered magmas (pomagmas)

record IsPomagma (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≲_
    mono           : Monotonic₂ _≲_ _≲_ _≲_ ∙

  open IsPartialOrder isPartialOrder public

  ∙-cong : Congruent₂ ∙
  ∙-cong = mono₂⇒cong₂ _≈_ _≈_ Eq.sym reflexive antisym mono

  isPromagma : IsPromagma ∙
  isPromagma = record
    { isPreorder = isPreorder
    ; ∙-cong     = ∙-cong
    ; mono       = mono
    }

  open IsPromagma isPromagma public
    using (setoid; ∙-congˡ; ∙-congʳ; monoˡ; monoʳ; isMagma)

-- Partially ordered semigroups (posemigroups)

record IsPosemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPomagma : IsPomagma ∙
    assoc     : Associative ∙

  open IsPomagma isPomagma public

  isProsemigroup : IsProsemigroup ∙
  isProsemigroup = record { isPromagma = isPromagma ; assoc = assoc }

  open IsProsemigroup isProsemigroup public using (isSemigroup)

-- Partially ordered monoids (pomonoids)

record IsPomonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPosemigroup : IsPosemigroup ∙
    identity      : Identity ε ∙

  open IsPosemigroup isPosemigroup public

  isPromonoid : IsPromonoid ∙ ε
  isPromonoid = record
    { isProsemigroup = isProsemigroup
    ; identity       = identity
    }

  open IsPromonoid isPromonoid public
    using (isMonoid; identityˡ; identityʳ)

-- Partially ordered commutative monoids (commutative pomonoids)

record IsCommutativePomonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPomonoid : IsPomonoid ∙ ε
    comm       : Commutative ∙

  open IsPomonoid isPomonoid public

  isCommutativePromonoid : IsCommutativePromonoid ∙ ε
  isCommutativePromonoid = record { isPromonoid = isPromonoid ; comm = comm }

  open IsCommutativePromonoid isCommutativePromonoid public
    using (isCommutativeMonoid; isCommutativeSemigroup)

-- Partially ordered semirings (posemirings)

record IsPosemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    +-isCommutativePomonoid : IsCommutativePomonoid + 0#
    *-mono                  : Monotonic₂ _≲_ _≲_ _≲_ *
    *-assoc                 : Associative *
    *-identity              : Identity 1# *
    distrib                 : * DistributesOver +
    zero                    : Zero 0# *

  open IsCommutativePomonoid +-isCommutativePomonoid public
    renaming
    ( assoc                  to +-assoc
    ; ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; mono                   to +-mono
    ; monoˡ                  to +-monoˡ
    ; monoʳ                  to +-monoʳ
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; comm                   to +-comm
    ; isMagma                to +-isMagma
    ; isPromagma             to +-isPromagma
    ; isPomagma              to +-isPomagma
    ; isSemigroup            to +-isSemigroup
    ; isProsemigroup         to +-isProsemigroup
    ; isPosemigroup          to +-isPosemigroup
    ; isMonoid               to +-isMonoid
    ; isPromonoid            to +-isPromonoid
    ; isPomonoid             to +-isPomonoid
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    ; isCommutativeMonoid    to +-isCommutativeMonoid
    ; isCommutativePromonoid to +-isCommutativePromonoid
    )

  *-isPomonoid : IsPomonoid * 1#
  *-isPomonoid = record
    { isPosemigroup      = record
      { isPomagma        = record
        { isPartialOrder = isPartialOrder
        ; mono           = *-mono
        }
      ; assoc            = *-assoc
      }
    ; identity           = *-identity
    }

  open IsPomonoid *-isPomonoid public
    using ()
    renaming
    ( ∙-cong         to *-cong
    ; ∙-congˡ        to *-congˡ
    ; ∙-congʳ        to *-congʳ
    ; monoˡ          to *-monoˡ
    ; monoʳ          to *-monoʳ
    ; identityˡ      to *-identityˡ
    ; identityʳ      to *-identityʳ
    ; isMagma        to *-isMagma
    ; isPromagma     to *-isPromagma
    ; isPomagma      to *-isPomagma
    ; isSemigroup    to *-isSemigroup
    ; isProsemigroup to *-isProsemigroup
    ; isPosemigroup  to *-isPosemigroup
    ; isMonoid       to *-isMonoid
    ; isPromonoid    to *-isPromonoid
    )

  isProsemiring : IsProsemiring + * 0# 1#
  isProsemiring = record
    { +-isCommutativePromonoid = +-isCommutativePromonoid
    ; *-cong                   = *-cong
    ; *-mono                   = *-mono
    ; *-assoc                  = *-assoc
    ; *-identity               = *-identity
    ; distrib                  = distrib
    ; zero                     = zero
    }

  open IsProsemiring isProsemiring public
    using (isSemiring; distribˡ; distribʳ; zeroˡ; zeroʳ)

record IsStarAuto {_⊗_ ε} (⊗-isCommutativePomonoid : IsCommutativePomonoid _⊗_ ε) (¬ : A → A)
   : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    ¬-mono     : ∀ {x y} → x ≲ y → ¬ y ≲ ¬ x
    involution : ∀ {x} → x ≈ ¬ (¬ x)

    *-aut   : ∀ {x y z} → (x ⊗ y) ≲ ¬ z → x ≲ ¬ (y ⊗ z)
    *-aut⁻¹ : ∀ {x y z} → x ≲ ¬ (y ⊗ z) → (x ⊗ y) ≲ ¬ z

  open IsCommutativePomonoid ⊗-isCommutativePomonoid
    using (refl; trans; reflexive; antisym; module Eq; setoid; isPartialOrder)
    renaming (mono to ⊗-mono; assoc to ⊗-assoc; comm to ⊗-comm;
              ∙-cong to ⊗-cong;
              identityˡ to ⊗-identityˡ;
              identityʳ to ⊗-identityʳ)

  ¬-cong : ∀ {x y} → x ≈ y → ¬ x ≈ ¬ y
  ¬-cong x≈y = antisym (¬-mono (reflexive (Eq.sym x≈y))) (¬-mono (reflexive x≈y))

  ⊥ : A
  ⊥ = ¬ ε

  _⅋_ : A → A → A
  x ⅋ y = ¬ (¬ x ⊗ ¬ y)

  ⅋-comm : ∀ x y → (x ⅋ y) ≈ (y ⅋ x)
  ⅋-comm x y = ¬-cong (⊗-comm _ _)

  ⅋-mono : Monotonic₂ _≲_ _≲_ _≲_ _⅋_
  ⅋-mono x≲y u≲v = ¬-mono (⊗-mono (¬-mono x≲y) (¬-mono u≲v))

  ⅋-assoc : Associative _⅋_
  ⅋-assoc x y z =
      begin
        (x ⅋ y) ⅋ z            ≡⟨⟩
        ¬ (¬ (x ⅋ y) ⊗ ¬ z)     ≈˘⟨ ¬-cong (⊗-cong involution Eq.refl) ⟩
        ¬ ((¬ x ⊗ ¬ y) ⊗ ¬ z)   ≈⟨ ¬-cong (⊗-assoc _ _ _) ⟩
        ¬ (¬ x ⊗ (¬ y ⊗ ¬ z))   ≈⟨ ¬-cong (⊗-cong Eq.refl involution) ⟩
        ¬ (¬ x ⊗ ¬ (y ⅋ z))     ≡⟨⟩
        x ⅋ (y ⅋ z)            ∎
     where open SetoidReasoning setoid

  ⅋-identityˡ : LeftIdentity ⊥ _⅋_
  ⅋-identityˡ x =
      begin
        ⊥ ⅋ x             ≡⟨⟩
        ¬ (¬ (¬ ε) ⊗ ¬ x)  ≈˘⟨ ¬-cong (⊗-cong involution Eq.refl) ⟩
        ¬ (ε ⊗ ¬ x)        ≈⟨ ¬-cong (⊗-identityˡ _) ⟩
        ¬ (¬ x)            ≈˘⟨ involution ⟩
        x                  ∎
      where open SetoidReasoning setoid

  ⅋-identityʳ : RightIdentity ⊥ _⅋_
  ⅋-identityʳ x =
      begin
        x ⅋ ⊥             ≡⟨⟩
        ¬ (¬ x ⊗ ¬ (¬ ε))  ≈˘⟨ ¬-cong (⊗-cong Eq.refl involution) ⟩
        ¬ (¬ x ⊗ ε)        ≈⟨ ¬-cong (⊗-identityʳ _) ⟩
        ¬ (¬ x)            ≈˘⟨ involution ⟩
        x                  ∎
      where open SetoidReasoning setoid

  ⅋-isCommutativePomonoid : IsCommutativePomonoid _⅋_ ⊥
  ⅋-isCommutativePomonoid = record {
    isPomonoid = record {
      isPosemigroup = record {
        isPomagma = record {
            isPartialOrder = isPartialOrder ;
            mono = ⅋-mono } ;
          assoc = ⅋-assoc } ;
        identity = ⅋-identityˡ , ⅋-identityʳ } ;
      comm = ⅋-comm }

  ev : ∀ {x} → (x ⊗ ¬ x) ≲ ⊥
  ev = *-aut⁻¹ (trans (reflexive involution) (¬-mono (reflexive (⊗-identityʳ _))))

  _⊸_ : A → A → A
  x ⊸ y = ¬ x ⅋ y

  ⊸-residualʳ-to : ∀ {x y z} → (x ⊗ y) ≲ z → y ≲ (x ⊸ z)
  ⊸-residualʳ-to xy≲z =
    *-aut (trans (reflexive (⊗-comm _ _)) (trans (⊗-mono (reflexive (Eq.sym involution)) refl) (trans xy≲z (reflexive involution))))

  ⊸-residualʳ-from : ∀ {x y z} → y ≲ (x ⊸ z) → (x ⊗ y) ≲ z
  ⊸-residualʳ-from y≲x⊸z =
    trans (reflexive (⊗-comm _ _))
          (trans (*-aut⁻¹ (trans y≲x⊸z (¬-mono (⊗-mono (reflexive involution) refl)))) (reflexive (Eq.sym involution)))

  ⊸-residualʳ : RightResidual _⊗_ _⊸_
  ⊸-residualʳ .Function.Equivalence.to = ⊸-residualʳ-to
  ⊸-residualʳ .Function.Equivalence.from = ⊸-residualʳ-from
  ⊸-residualʳ .Function.Equivalence.to-cong PropEq.refl = PropEq.refl
  ⊸-residualʳ .Function.Equivalence.from-cong PropEq.refl = PropEq.refl

  eval : ∀ {x y} → ((x ⅋ y) ⊗ ¬ y) ≲ x
  eval = trans (reflexive (⊗-comm _ _))
               (⊸-residualʳ-from (trans (reflexive (⅋-comm _ _))
                                         (⅋-mono (reflexive involution) refl)))

  coev : ∀ {x} → ε ≲ (x ⅋ ¬ x)
  coev {x} = trans (⊸-residualʳ-to (reflexive (⊗-identityʳ x))) (reflexive (⅋-comm _ _))

  linear-distrib : ∀ {x y z} → (x ⊗ (y ⅋ z)) ≲ ((x ⊗ y) ⅋ z)
  linear-distrib =
    trans (*-aut (trans (reflexive (⊗-assoc _ _ _))
                  (trans (⊗-mono refl eval)
                          (reflexive involution))))
          (reflexive (⅋-comm _ _))
