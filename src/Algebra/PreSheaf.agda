{-# OPTIONS --postfix-projections --safe --without-K #-}

open import Level
open import Algebra
open import Algebra.Ordered.Consequences
open import Algebra.Ordered.Definitions
open import Algebra.Ordered.Structures
open import Algebra.Ordered.Structures.Residuated
open import Algebra.Ordered.Structures.Duoidal
open import Function using (flip)
open import Data.Product using (_×_; _,_; -,_; proj₁; proj₂; ∃-syntax; Σ-syntax; swap; <_,_>)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤; tt)
open import Relation.Binary
open import Relation.Binary.Construct.Core.Symmetric as SymCore using (SymCore)
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.Construct.Flip.EqAndOrd as Flip
open import Relation.Unary using (Pred; _⊆_)

module Algebra.PreSheaf {c ℓ₁ ℓ₂} (poset : Poset c ℓ₁ ℓ₂) where

open Poset poset
  using
    ( Carrier
    ; _≈_
    ; _≤_
    )
  renaming
    ( refl  to ≤-refl
    ; trans to ≤-trans
    )

private
  variable
    w x y z : Carrier

record PreSheaf : Set (suc (c ⊔ ℓ₂)) where
  no-eta-equality
  field
    ICarrier : Pred Carrier (c ⊔ ℓ₂)
    ≤-closed : x ≤ y → ICarrier y → ICarrier x
open PreSheaf public

private
  variable
    F F₁ F₂ : PreSheaf
    G G₁ G₂ : PreSheaf
    H H₁ H₂ : PreSheaf

infix 4 _≤ᵖ_

record _≤ᵖ_ (F G : PreSheaf) : Set (c ⊔ ℓ₂) where
  no-eta-equality
  constructor mk-≤ᵖ
  field
    *≤ᵖ* : F .ICarrier ⊆ G .ICarrier
open _≤ᵖ_ public

infix 4 _≥ᵖ_

_≥ᵖ_ : PreSheaf → PreSheaf → Set (c ⊔ ℓ₂)
_≥ᵖ_ = flip _≤ᵖ_

infix 4 _≈ᵖ_

_≈ᵖ_ : PreSheaf → PreSheaf → Set (c ⊔ ℓ₂)
_≈ᵖ_ = SymCore _≤ᵖ_

≤ᵖ-refl : Reflexive _≤ᵖ_
≤ᵖ-refl .*≤ᵖ* Fx = Fx

≤ᵖ-trans : Transitive _≤ᵖ_
≤ᵖ-trans F≤G G≤H .*≤ᵖ* Fx = G≤H .*≤ᵖ* (F≤G .*≤ᵖ* Fx)

≤ᵖ-isPartialOrder : IsPartialOrder _≈ᵖ_ _≤ᵖ_
≤ᵖ-isPartialOrder = SymCore.isPreorder⇒isPartialOrder _≤ᵖ_ ≡-≤ᵖ-isPreorder
  where
    ≡-≤ᵖ-isPreorder : IsPreorder _≡_ _≤ᵖ_
    ≡-≤ᵖ-isPreorder = record
      { isEquivalence = PropEq.isEquivalence
      ; reflexive = λ { PropEq.refl → ≤ᵖ-refl }
      ; trans = ≤ᵖ-trans
      }

open IsPartialOrder ≤ᵖ-isPartialOrder
  using ()
  renaming
    ( isPreorder to ≤ᵖ-isPreorder
    )

≤ᵖ-poset : Poset _ _ _
≤ᵖ-poset = record
  { isPartialOrder = ≤ᵖ-isPartialOrder
  }

module Reasoning where
  open import Relation.Binary.Reasoning.PartialOrder ≤ᵖ-poset public
    using
      ( begin_
      ; _∎
      )
    renaming
      ( ≤-go to ≤ˢ-go
      ; ≈-go to ≈ˢ-go
      )
  step-≤ˢ = ≤ˢ-go
  syntax step-≤ˢ x yRz x≤y = x ≤ˢ⟨ x≤y ⟩ yRz
  step-≈ˢ = ≈ˢ-go
  syntax step-≈ˢ x yRz x≈y = x ≈ˢ⟨ x≈y ⟩ yRz

≥ᵖ-isPartialOrder : IsPartialOrder _≈ᵖ_ _≥ᵖ_
≥ᵖ-isPartialOrder = Flip.isPartialOrder ≤ᵖ-isPartialOrder

ηᵖ : Carrier → PreSheaf
ηᵖ x .ICarrier y = Lift c (y ≤ x)
ηᵖ x .≤-closed z≤y y≤x = lift (≤-trans z≤y (y≤x .lower))

------------------------------------------------------------------------------
-- Construct a meet semilattice for presheaves

_∧ᵖ_ : PreSheaf → PreSheaf → PreSheaf
(F ∧ᵖ G) .ICarrier x = F .ICarrier x × G .ICarrier x
(F ∧ᵖ G) .≤-closed x≤y (Fy , Gy) = (F .≤-closed x≤y Fy , G .≤-closed x≤y Gy)

proj₁ᵖ : (F ∧ᵖ G) ≤ᵖ F
proj₁ᵖ .*≤ᵖ* = proj₁

proj₂ᵖ : (F ∧ᵖ G) ≤ᵖ G
proj₂ᵖ .*≤ᵖ* = proj₂

⟨_,_⟩ᵖ : F ≤ᵖ G → F ≤ᵖ H → F ≤ᵖ (G ∧ᵖ H)
⟨ H≤F , H≤G ⟩ᵖ .*≤ᵖ* = < H≤F .*≤ᵖ* , H≤G .*≤ᵖ* >

∧ᵖ-isMeetSemilattice : IsMeetSemilattice _≈ᵖ_ _≤ᵖ_ _∧ᵖ_
∧ᵖ-isMeetSemilattice = record
  { isPartialOrder = ≤ᵖ-isPartialOrder
  ; infimum        = λ F G → (proj₁ᵖ , proj₂ᵖ , λ H → ⟨_,_⟩ᵖ)
  }

∧ᵖ-meetSemilattice : MeetSemilattice _ _ _
∧ᵖ-meetSemilattice = record
  { isMeetSemilattice = ∧ᵖ-isMeetSemilattice
  }

open import Relation.Binary.Lattice.Properties.MeetSemilattice ∧ᵖ-meetSemilattice
  using ()
  renaming
    ( ∧-monotonic to ∧ᵖ-monotonic
    ; ∧-assoc     to ∧ᵖ-assoc
    ; ∧-comm      to ∧ᵖ-comm
    )

∧ᵖ-⊤ᵖ-isPosemigroup : IsPosemigroup _≈ᵖ_ _≤ᵖ_ _∧ᵖ_
∧ᵖ-⊤ᵖ-isPosemigroup = record
  { isPomagma = record 
    { isPartialOrder = ≤ᵖ-isPartialOrder
    ; mono = ∧ᵖ-monotonic
    }
  ; assoc = ∧ᵖ-assoc
  }

⊤ᵖ : PreSheaf
⊤ᵖ .ICarrier x = Lift (c ⊔ ℓ₂) ⊤
⊤ᵖ .≤-closed x Fx = Fx

∧ᵖ-⊤ᵖ-isBoundedMeetSemilattice : IsBoundedMeetSemilattice _≈ᵖ_ _≤ᵖ_ _∧ᵖ_ ⊤ᵖ
∧ᵖ-⊤ᵖ-isBoundedMeetSemilattice = record
  { isMeetSemilattice = ∧ᵖ-isMeetSemilattice
  ; maximum           = λ F → mk-≤ᵖ (λ Fx → lift tt)
  }

∧ᵖ-⊤ᵖ-boundedMeetSemilattice : BoundedMeetSemilattice _ _ _
∧ᵖ-⊤ᵖ-boundedMeetSemilattice = record
  { isBoundedMeetSemilattice = ∧ᵖ-⊤ᵖ-isBoundedMeetSemilattice
  }

open import Relation.Binary.Lattice.Properties.BoundedMeetSemilattice ∧ᵖ-⊤ᵖ-boundedMeetSemilattice
  using ()
  renaming
    ( identity to ∧ᵖ-⊤ᵖ-identity
    )

∧ᵖ-⊤ᵖ-isCommutativePomonoid : IsCommutativePomonoid _≈ᵖ_ _≤ᵖ_ _∧ᵖ_ ⊤ᵖ
∧ᵖ-⊤ᵖ-isCommutativePomonoid = record
  { isPomonoid = record
    { isPosemigroup = ∧ᵖ-⊤ᵖ-isPosemigroup
    ; identity = ∧ᵖ-⊤ᵖ-identity
    }
  ; comm = ∧ᵖ-comm
  }

-- ------------------------------------------------------------------------------
-- -- Construct a join semilattice for presheaves

_∨ᵖ_ : PreSheaf → PreSheaf → PreSheaf
(F ∨ᵖ G) .ICarrier x = F .ICarrier x ⊎ G .ICarrier x
(F ∨ᵖ G) .≤-closed x≤y (inj₁ Fy) = inj₁ (F .≤-closed x≤y Fy)
(F ∨ᵖ G) .≤-closed x≤y (inj₂ Gy) = inj₂ (G .≤-closed x≤y Gy)

inj₁ᵖ : F ≤ᵖ (F ∨ᵖ G)
inj₁ᵖ .*≤ᵖ* = inj₁

inj₂ᵖ : G ≤ᵖ (F ∨ᵖ G)
inj₂ᵖ .*≤ᵖ* = inj₂

[_,_]ᵖ : F ≤ᵖ H → G ≤ᵖ H → (F ∨ᵖ G) ≤ᵖ H
[ H≥F , H≥G ]ᵖ .*≤ᵖ* = [ H≥F .*≤ᵖ* , H≥G .*≤ᵖ* ]

∨ᵖ-isJoinSemilattice : IsJoinSemilattice _≈ᵖ_ _≤ᵖ_ _∨ᵖ_
∨ᵖ-isJoinSemilattice = record
  { isPartialOrder = ≤ᵖ-isPartialOrder
  ; supremum       = λ F G → (inj₁ᵖ , inj₂ᵖ , λ H → [_,_]ᵖ)
  }

open IsJoinSemilattice ∨ᵖ-isJoinSemilattice
  using ()
  renaming
    ( supremum to ∨ᵖ-supremum
    )

-- ------------------------------------------------------------------------------
-- -- Construct a residuated pomonoid for presheaves

_⇒ᵖ_ : PreSheaf → PreSheaf → PreSheaf
(F ⇒ᵖ G) .ICarrier x = ∀ {y} → y ≤ x → F .ICarrier y → G .ICarrier y
(F ⇒ᵖ G) .≤-closed x≤y f z≤x Fz = f (≤-trans z≤x x≤y) Fz

⇒ᵖ-residualʳ-to : (F ∧ᵖ G) ≤ᵖ H → G ≤ᵖ (F ⇒ᵖ H)
⇒ᵖ-residualʳ-to {F} {G} {H} F∧G≤H .*≤ᵖ* Gx y≤x Fy = F∧G≤H .*≤ᵖ* (Fy , G .≤-closed y≤x Gx)

⇒ᵖ-residualʳ-from : G ≤ᵖ (F ⇒ᵖ H) → (F ∧ᵖ G) ≤ᵖ H
⇒ᵖ-residualʳ-from G≤F⇒H .*≤ᵖ* (Fx , Gx) = G≤F⇒H .*≤ᵖ* Gx ≤-refl Fx

⇒ᵖ-residualʳ : RightResidual _≤ᵖ_ _∧ᵖ_ _⇒ᵖ_
⇒ᵖ-residualʳ .Function.Equivalence.to        = ⇒ᵖ-residualʳ-to
⇒ᵖ-residualʳ .Function.Equivalence.from      = ⇒ᵖ-residualʳ-from
⇒ᵖ-residualʳ .Function.Equivalence.to-cong   = λ { PropEq.refl → PropEq.refl }
⇒ᵖ-residualʳ .Function.Equivalence.from-cong = λ { PropEq.refl → PropEq.refl }

⇒ᵖ-∧ᵖ-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈ᵖ_ _≤ᵖ_ _∧ᵖ_ _⇒ᵖ_ ⊤ᵖ
⇒ᵖ-∧ᵖ-isResiduatedCommutativePomonoid = record
  { isCommutativePomonoid = ∧ᵖ-⊤ᵖ-isCommutativePomonoid
  ; residuated            = comm∧residual⇒residuated ≤ᵖ-isPreorder ∧ᵖ-comm ⇒ᵖ-residualʳ
  }

------------------------------------------------------------------------------
-- Lift monoids to presheaves

module LiftIsPomonoid {_∙_} {ε} (isPomonoid : IsPomonoid _≈_ _≤_ _∙_ ε) where

  open IsPomonoid isPomonoid

  _∙ᵖ_ : PreSheaf → PreSheaf → PreSheaf
  (F ∙ᵖ G) .ICarrier x =
    ∃[ y ] ∃[ z ] (x ≤ (y ∙ z) × F .ICarrier y × G .ICarrier z)
  (F ∙ᵖ G) .≤-closed x≤w (y , z , w≤yz , ϕ₁ , ϕ₂) =
    (-, -, ≤-trans x≤w w≤yz , ϕ₁ , ϕ₂)

  ∙ᵖ-mono : Monotonic₂ _≤ᵖ_ _≤ᵖ_ _≤ᵖ_ _∙ᵖ_
  ∙ᵖ-mono F₁≤F₂ G₁≤G₂ .*≤ᵖ* (y , z , x≤yz , F₁y , G₁z) =
    (-, -, x≤yz , F₁≤F₂ .*≤ᵖ* F₁y , G₁≤G₂ .*≤ᵖ* G₁z)

  εᵖ : PreSheaf
  εᵖ = ηᵖ ε

  ∙ᵖ-identityˡ : LeftIdentity _≈ᵖ_ εᵖ _∙ᵖ_
  ∙ᵖ-identityˡ F .proj₁ .*≤ᵖ* (y , z , x≤yz , lift y≤ε , Fz) =
    F .≤-closed (≤-trans x≤yz (≤-trans (mono y≤ε ≤-refl) (≤-respʳ-≈ (identityˡ z) ≤-refl) )) Fz
  ∙ᵖ-identityˡ F .proj₂ .*≤ᵖ* Fx =
    (-, -, ≤-respˡ-≈ (identityˡ _) ≤-refl , lift ≤-refl , Fx)

  ∙ᵖ-identityʳ : RightIdentity _≈ᵖ_ εᵖ _∙ᵖ_
  ∙ᵖ-identityʳ F .proj₁ .*≤ᵖ* (y , z , x≤yz , Fy , lift z≤ε) =
    F .≤-closed (≤-trans x≤yz (≤-trans (mono ≤-refl z≤ε) (≤-respʳ-≈ (identityʳ y) ≤-refl) )) Fy
  ∙ᵖ-identityʳ F .proj₂ .*≤ᵖ* Fx =
    (-, -, ≤-respˡ-≈ (identityʳ _) ≤-refl , Fx , lift ≤-refl)

  ∙ᵖ-identity : Identity _≈ᵖ_ εᵖ _∙ᵖ_
  ∙ᵖ-identity = (∙ᵖ-identityˡ , ∙ᵖ-identityʳ)

  ∙ᵖ-assoc : Associative _≈ᵖ_ _∙ᵖ_
  ∙ᵖ-assoc F G H .proj₁ .*≤ᵖ* (y , z , x≤yz , (u , v , y≤uv , Fu , Gv) , Hz) =
    let x≤u∙v∙z = ≤-trans x≤yz (≤-trans (mono y≤uv ≤-refl) (≤-respʳ-≈ (assoc u v z)  ≤-refl)) in
      (-, -, x≤u∙v∙z , Fu , (-, -, ≤-refl , Gv , Hz))

  ∙ᵖ-assoc F G H .proj₂ .*≤ᵖ* (y , z , x≤yz , Fy , (u , v , z≤uv , Gu , Hv)) =
    let x≤y∙u∙v = ≤-trans x≤yz (≤-trans (mono ≤-refl z≤uv) (≤-respˡ-≈ (assoc y u v) ≤-refl)) in
      (-, -, x≤y∙u∙v , (-, -, ≤-refl , Fy , Gu) , Hv)

  ∙ᵖ-isPomonoid : IsPomonoid _≈ᵖ_ _≤ᵖ_ _∙ᵖ_ εᵖ
  ∙ᵖ-isPomonoid = record
    { isPosemigroup = record
      { isPomagma = record
        { isPartialOrder = ≤ᵖ-isPartialOrder
        ; mono = ∙ᵖ-mono
        }
      ; assoc = ∙ᵖ-assoc
      }
    ; identity = ∙ᵖ-identity
    }

  open IsPomonoid ∙ᵖ-isPomonoid public
    using
      (
      )
    renaming
      ( monoˡ   to ∙ᵖ-monoˡ
      ; monoʳ   to ∙ᵖ-monoʳ
      ; ∙-cong  to ∙ᵖ-cong
      ; ∙-congˡ to ∙ᵖ-congˡ
      ; ∙-congʳ to ∙ᵖ-congʳ
      )

module LiftIsCommutativePomonoid {_∙_} {ε} (isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∙_ ε) where

  open IsCommutativePomonoid isCommutativePomonoid
  open LiftIsPomonoid isPomonoid public

  ∙ᵖ-comm : Commutative _≈ᵖ_ _∙ᵖ_
  ∙ᵖ-comm F G .proj₁ .*≤ᵖ* (y , z , x≤yz , Fy , Gz) = 
    (-, -, trans x≤yz (≤-respˡ-≈ (comm z y) ≤-refl) , Gz , Fy)
  ∙ᵖ-comm F G .proj₂ .*≤ᵖ* (y , z , x≤yz , Gy , Fz) = 
    (-, -, trans x≤yz (≤-respˡ-≈ (comm z y) ≤-refl) , Fz , Gy)

  ∙ᵖ-isCommutativePomonoid : IsCommutativePomonoid _≈ᵖ_ _≤ᵖ_ _∙ᵖ_ εᵖ
  ∙ᵖ-isCommutativePomonoid = record
    { isPomonoid = ∙ᵖ-isPomonoid
    ; comm       = ∙ᵖ-comm 
    }

  _⇨ᵖ_ : PreSheaf → PreSheaf → PreSheaf
  (F ⇨ᵖ G) .ICarrier x        = ∀ {y} → F .ICarrier y → G .ICarrier (x ∙ y)
  (F ⇨ᵖ G) .≤-closed x≤z f Fy = G .≤-closed (mono x≤z refl) (f Fy)

  ⇨ᵖ-residual-to : (F ∙ᵖ G) ≤ᵖ H → G ≤ᵖ (F ⇨ᵖ H)
  ⇨ᵖ-residual-to F∙G≤H .*≤ᵖ* Gx Fy = 
    F∙G≤H .*≤ᵖ* (-, -, ≤-respˡ-≈ (comm _ _) ≤-refl , Fy , Gx)

  ⇨ᵖ-residual-from : G ≤ᵖ (F ⇨ᵖ H) → (F ∙ᵖ G) ≤ᵖ H
  ⇨ᵖ-residual-from {G} {F} {H} G≤F⇨H .*≤ᵖ* (_ , _ , x≤y∙z , Fy , Gz) = 
    H .≤-closed (trans x≤y∙z (≤-respˡ-≈ (comm _ _) ≤-refl)) (G≤F⇨H .*≤ᵖ* Gz Fy)

  ⇨ᵖ-residual : RightResidual _≤ᵖ_ _∙ᵖ_ _⇨ᵖ_
  ⇨ᵖ-residual .Function.Equivalence.to        = ⇨ᵖ-residual-to
  ⇨ᵖ-residual .Function.Equivalence.from      = ⇨ᵖ-residual-from
  ⇨ᵖ-residual .Function.Equivalence.to-cong   = λ { PropEq.refl → PropEq.refl }
  ⇨ᵖ-residual .Function.Equivalence.from-cong = λ { PropEq.refl → PropEq.refl }

  ⇨ᵖ-∙ᵖ-isResiduatedCommutativePomonoid : IsResiduatedCommutativePomonoid _≈ᵖ_ _≤ᵖ_ _∙ᵖ_ _⇨ᵖ_ εᵖ
  ⇨ᵖ-∙ᵖ-isResiduatedCommutativePomonoid = record 
    { isCommutativePomonoid = ∙ᵖ-isCommutativePomonoid 
    ; residuated = comm∧residual⇒residuated ≤ᵖ-isPreorder ∙ᵖ-comm ⇨ᵖ-residual 
    }

  ∙ᵖ-∨ᵖ-distrib : _DistributesOver_ _≤ᵖ_ _∙ᵖ_ _∨ᵖ_
  ∙ᵖ-∨ᵖ-distrib = supremum∧residuated⇒distrib ≤ᵖ-isPreorder ∨ᵖ-supremum 
    (IsResiduatedCommutativePomonoid.residuated ⇨ᵖ-∙ᵖ-isResiduatedCommutativePomonoid)

module LiftIsDuoidal {_∙_} {_▷_} {ε} {ι} (isDuoidal : IsDuoidal _≈_ _≤_ _∙_ _▷_ ε ι) where

  open IsDuoidal isDuoidal
  open LiftIsPomonoid ∙-isPomonoid public
  open LiftIsPomonoid ▷-isPomonoid public
    renaming
      ( _∙ᵖ_          to _▷ᵖ_
      ; εᵖ            to ιᵖ
      ; ∙ᵖ-mono       to ▷ᵖ-mono
      ; ∙ᵖ-monoˡ      to ▷ᵖ-monoˡ
      ; ∙ᵖ-monoʳ      to ▷ᵖ-monoʳ
      ; ∙ᵖ-cong       to ▷ᵖ-cong
      ; ∙ᵖ-congˡ      to ▷ᵖ-congˡ
      ; ∙ᵖ-congʳ      to ▷ᵖ-congʳ
      ; ∙ᵖ-assoc      to ▷ᵖ-assoc
      ; ∙ᵖ-identity   to ▷ᵖ-identity
      ; ∙ᵖ-identityˡ  to ▷ᵖ-identityˡ
      ; ∙ᵖ-identityʳ  to ▷ᵖ-identityʳ
      ; ∙ᵖ-isPomonoid to ▷ᵖ-isPomonoid
      )

  ∙ᵖ-▷ᵖ-entropy : Entropy _≤ᵖ_ _∙ᵖ_ _▷ᵖ_
  ∙ᵖ-▷ᵖ-entropy F₁ G₁ F₂ G₂ .*≤ᵖ*
    (y , z , x≤yz ,
      (y₁ , y₂ , y≤y₁y₂ , F₁y₁ , G₁y₂) ,
      (z₁ , z₂ , z≤z₁z₂ , F₂z₁ , G₂z₂)) =
    (-, -, trans x≤yz (trans (∙-mono y≤y₁y₂ z≤z₁z₂) (∙-▷-entropy y₁ y₂ z₁ z₂)) ,
      (-, -, refl , F₁y₁ , F₂z₁) ,
      (-, -, refl , G₁y₂ , G₂z₂))

  ∙ᵖ-idem-ιᵖ : _SubidempotentOn_ _≤ᵖ_ _∙ᵖ_ ιᵖ
  ∙ᵖ-idem-ιᵖ .*≤ᵖ* (y , z , x≤y∙z , ιy , ιz) .lower =
    trans x≤y∙z (trans (∙-mono (ιy .lower) (ιz .lower)) ∙-idem-ι)

  ▷ᵖ-idem-εᵖ : _SuperidempotentOn_ _≤ᵖ_ _▷ᵖ_ εᵖ
  ▷ᵖ-idem-εᵖ .*≤ᵖ* εx =
    (-, -, trans (εx .lower) ▷-idem-ε , lift refl , lift refl)

  εᵖ≤ιᵖ : εᵖ ≤ᵖ ιᵖ
  εᵖ≤ιᵖ .*≤ᵖ* εx .lower = trans (εx .lower) ε≲ι

  ∙ᵖ-▷ᵖ-isDuoidal : IsDuoidal _≈ᵖ_ _≤ᵖ_ _∙ᵖ_ _▷ᵖ_ εᵖ ιᵖ
  ∙ᵖ-▷ᵖ-isDuoidal = record
    { ∙-isPomonoid = ∙ᵖ-isPomonoid
    ; ▷-isPomonoid = ▷ᵖ-isPomonoid
    ; ∙-▷-entropy  = ∙ᵖ-▷ᵖ-entropy
    ; ∙-idem-ι     = ∙ᵖ-idem-ιᵖ
    ; ▷-idem-ε     = ▷ᵖ-idem-εᵖ
    ; ε≲ι          = εᵖ≤ιᵖ
    }
