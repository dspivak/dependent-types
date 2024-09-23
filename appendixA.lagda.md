```agda
{-# OPTIONS --without-K --rewriting #-}
module appendixA where

open import part1v2
open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import part2v2
```

```agda
transpAp : ∀ {ℓ ℓ' κ} {A : Type ℓ} {A' : Type ℓ'} {a b : A}
           → (B : A' → Type κ) (f : A → A') (e : a ≡ b) (x : B (f a))
           → transp (λ x → B (f x)) e x ≡ transp B (ap f e) x
transpAp B f refl x = refl

•invr : ∀ {ℓ} {A : Type ℓ} {a b : A}
        → (e : a ≡ b) → (sym e) • e ≡ refl
•invr refl = refl

≡siml : ∀ {ℓ} {A : Type ℓ} {a b : A}
        → (e : a ≡ b) → refl ≡ (b ≡〈 sym e 〉 e)
≡siml refl = refl

≡idr : ∀ {ℓ} {A : Type ℓ} {a b : A}
       → (e : a ≡ b) → e ≡ (a ≡〈 refl 〉 e)
≡idr refl = refl

conj : ∀ {ℓ} {A : Type ℓ} {a b c d : A}
       → (e1 : a ≡ b) (e2 : a ≡ c) (e3 : b ≡ d) (e4 : c ≡ d)
       → (a ≡〈 e1 〉 e3) ≡ (a ≡〈 e2 〉 e4)
       → e3 ≡ (b ≡〈 sym e1 〉(a ≡〈 e2 〉 e4))
conj e1 e2 refl refl refl = ≡siml e1

nat : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} {f g : A → B} {a b : A}
      → (α : (x : A) → f x ≡ g x) (e : a ≡ b)
      → ((f a) ≡〈 α a 〉 (ap g e)) ≡ ((f a) ≡〈 ap f e 〉 (α b))
nat {a = a} α refl = ≡idr (α a)

cancel : ∀ {ℓ} {A : Type ℓ} {a b c : A}
         → (e1 e2 : a ≡ b) (e3 : b ≡ c)
         → (a ≡〈 e1 〉 e3) ≡ (a ≡〈 e2 〉 e3)
         → e1 ≡ e2
cancel e1 e2 refl refl = refl

apId : ∀ {ℓ} {A : Type ℓ} {a b : A}
       → (e : a ≡ b) → ap (λ x → x) e ≡ e
apId refl = refl

apComp : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {a b : A}
         → (f : A → B) (g : B → C) (e : a ≡ b)
         → ap (λ x → g (f x)) e ≡ ap g (ap f e)
apComp f g refl = refl

apHtpy : ∀ {ℓ} {A : Type ℓ} {a : A}
         → (i : A → A) (α : (x : A) → i x ≡ x)
         → ap i (α a) ≡ α (i a)
apHtpy {a = a} i α = 
    cancel (ap i (α a)) (α (i a)) (α a) 
           ((i (i a) ≡〈 ap i (α a) 〉 α a) 
           ≡〈 sym (nat α (α a)) 〉 
           ((i (i a) ≡〈 α (i a) 〉 ap (λ z → z) (α a)) 
           ≡〈 ap (λ e → i (i a) ≡〈 α (i a) 〉 e) (apId (α a)) 〉 
           ((i (i a) ≡〈 α (i a) 〉 α a) □)))

HAdj : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ}
       → (A → B) → Set (ℓ ⊔ κ)
HAdj {A = A} {B = B} f =
    Σ (B → A) (λ g → 
      Σ ((x : A) → g (f x) ≡ x) (λ η → 
        Σ ((y : B) → f (g y) ≡ y) (λ ε → 
          (x : A) → ap f (η x) ≡ ε (f x))))

Iso→HAdj : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} {f : A → B}
           → Iso f → HAdj f
Iso→HAdj {f = f} (g , η , ε) =
    g , (η 
    , ( (λ y → 
           f (g y)         ≡〈 sym (ε (f (g y))) 〉 
          (f (g (f (g y))) ≡〈 ap f (η (g y)) 〉 
          (f (g y)         ≡〈 ε y 〉 
          (y               □)))) 
      , λ x → conj (ε (f (g (f x)))) (ap f (η (g (f x)))) 
                   (ap f (η x)) (ε (f x)) 
                   (((f (g (f (g (f x)))) ≡〈 ε (f (g (f x))) 〉 ap f (η x))) 
                    ≡〈 nat (λ z → ε (f z)) (η x) 〉 
                    (((f (g (f (g (f x)))) ≡〈 ap (λ z → f (g (f z))) (η x) 〉 ε (f x))) 
                    ≡〈 ap (λ e → (f (g (f (g (f x)))) ≡〈 e 〉 ε (f x))) 
                          ((ap (λ z → f (g (f z))) (η x)) 
                           ≡〈 apComp (λ z → g (f z)) f (η x) 〉 
                           ((ap f (ap (λ z → g (f z)) (η x))) 
                           ≡〈 ap (ap f) (apHtpy (λ z → g (f z)) η) 〉 
                           (ap f (η (g (f x))) □))) 〉 
                    (((f (g (f (g (f x)))) ≡〈 ap f (η (g (f x))) 〉 ε (f x))) □)))))

pairEquiv1 : ∀ {ℓ ℓ' κ} {A : Type ℓ} {A' : Type ℓ'} {B : A' → Type κ}
             → (f : A → A') → isEquiv f
             → isEquiv {A = Σ A (λ x → B (f x))} {B = Σ A' B} 
                       (λ (x , y) → (f x , y))
pairEquiv1 {A = A} {A' = A'} {B = B} f ef =
  Iso→isEquiv
    ( (λ (x , y) → (g x , transp B (sym (ε x)) y))
    , ( (λ (x , y) → pairEq (η x) (lemma x y)) 
      , λ (x , y) → pairEq (ε x) (symr (ε x) y) ) )
  where
    g : A' → A
    g = fst (Iso→HAdj (isEquiv→Iso ef))
    η : (x : A) → g (f x) ≡ x
    η = fst (snd (Iso→HAdj (isEquiv→Iso ef)))
    ε : (y : A') → f (g y) ≡ y
    ε = fst (snd (snd (Iso→HAdj (isEquiv→Iso ef))))
    ρ : (x : A) → ap f (η x) ≡ ε (f x)
    ρ = snd (snd (snd (Iso→HAdj (isEquiv→Iso ef))))
    lemma : (x : A) (y : B (f x))
            → transp (λ z → B (f z)) (η x)
                     (transp B (sym (ε (f x))) y)
              ≡ y
    lemma x y = (transp (λ z → B (f z)) (η x) 
                        (transp B (sym (ε (f x))) y)) 
                ≡〈 transpAp B f (η x) 
                            (transp B (sym (ε (f x))) y) 〉 
                ( transp B (ap f (η x)) 
                           (transp B (sym (ε (f x))) y) 
                ≡〈 ap (λ e → transp B e 
                                (transp B (sym (ε (f x))) y)) 
                      (ρ x) 〉 
                ( (transp B (ε (f x)) 
                          (transp B (sym (ε (f x))) y)) 
                ≡〈 (symr (ε (f x)) y) 〉 
                (y □)))

pairEquiv2 : ∀ {ℓ κ κ'} {A : Type ℓ} {B : A → Type κ} {B' : A → Type κ'}
             → (g : (x : A) → B x → B' x) → ((x : A) → isEquiv (g x))
             → isEquiv {A = Σ A B} {B = Σ A B'}
                       (λ (x , y) → (x , g x y))
pairEquiv2 g eg =
    let isog = (λ x → isEquiv→Iso (eg x)) 
    in Iso→isEquiv ( (λ (x , y) → (x , fst (isog x) y)) 
                   , ( (λ (x , y) → 
                          pairEq refl (fst (snd (isog x)) y)) 
                     , λ (x , y) → 
                         pairEq refl (snd (snd (isog x)) y)))

pairEquiv : ∀ {ℓ ℓ' κ κ'} {A : Type ℓ} {A' : Type ℓ'}
            → {B : A → Type κ} {B' : A' → Type κ'}
            → (f : A → A') (g : (x : A) → B x → B' (f x))
            → isEquiv f → ((x : A) → isEquiv (g x))
            → isEquiv {A = Σ A B} {B = Σ A' B'}
                      (λ (x , y) → (f x , g x y))
pairEquiv f g ef eg = 
    compIsEquiv (pairEquiv1 f ef) 
                (pairEquiv2 g eg)

J : ∀ {ℓ κ} {A : Type ℓ} {a : A} (B : (x : A) → a ≡ x → Type κ)
    → {a' : A} (e : a ≡ a') → B a refl → B a' e
J B refl b = b

transpPre : ∀ {ℓ0 ℓ1 κ0 κ1} {A : Type ℓ0} {a a' : A} {B : A → Type κ0}
              {C : Type ℓ1} {D : C → Type κ1} {f : A → C}
              (mf : isMono f) (g : (x : A) → B x → D (f x))
              (e : f a ≡ f a') {b : B a}
              → transp D e (g a b) ≡ g a' (transp B (inv mf e) b)
transpPre {a = a} {a' = a'} {B = B} {D = D} {f = f} mf g e {b = b} = 
    transp D e (g a b)  
        ≡〈 ap (λ e' → transp D e' (g a b)) (sym (snd (snd mf) e)) 〉 
    ( _ ≡〈 (J (λ x e' → transp D (ap f e') (g a b) ≡ g x (transp B e' b)) 
               (inv mf e) refl) 〉 
    ((g a' (transp B (inv mf e) b)) □))

postulate
    funext : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {f g : (x : A) → B x}
             → ((x : A) → f x ≡ g x) → f ≡ g
    funextr : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {f g : (x : A) → B x}
              → (e : (x : A) → f x ≡ g x) → coAp (funext e) ≡ e
    funextl : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {f g : (x : A) → B x}
              → (e : f ≡ g) → funext (coAp e) ≡ e

transpD : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {a a' : A}
          → (f : (x : A) → B x) (e : a ≡ a')
          → transp B e (f a) ≡ f a'
transpD f refl = refl

transpHAdj : ∀ {ℓ ℓ' κ} {A : Type ℓ} {B : Type ℓ'} 
            → {C : B → Type κ} {a : A}
            → {g : A → B} {h : B → A} 
            → (f : (x : A) → C (g x)) 
            → (e : (y : B) → g (h y) ≡ y)
            → (e' : (x : A) → h (g x) ≡ x)
            → (e'' : (x : A) → e (g x) ≡ ap g (e' x))
            → transp C (e (g a)) (f (h (g a))) ≡ f a
transpHAdj {C = C} {a = a} {g = g} {h = h} f e e' e'' = 
    transp C (e (g a)) (f (h (g a)))               
        ≡〈 ap (λ ee → transp C ee (f (h (g a)))) (e'' a) 〉 
    (transp C (ap g (e' a)) (f (h (g a))) 
        ≡〈 sym (transpAp C g (e' a) (f (h (g a)))) 〉 
    ((transp (λ x → C (g x)) (e' a) (f (h (g a)))) 
        ≡〈 transpD f (e' a) 〉
    ((f a) □)))

PreCompEquiv : ∀ {ℓ ℓ' κ} {A : Type ℓ} {B : Type ℓ'} {C : B → Type κ}
               → (f : A → B) → isEquiv f 
               → isEquiv {A = (b : B) → C b} 
                         {B = (a : A) → C (f a)} 
                         (λ g → λ a → g (f a))
PreCompEquiv {C = C} f ef =
    let (f⁻¹ , l , r , e) = Iso→HAdj (isEquiv→Iso ef) 
    in Iso→isEquiv ( (λ g b → transp C (r b) (g (f⁻¹ b))) 
                   , ( (λ g → funext (λ b → transpD g (r b))) 
                     , λ g → funext (λ a → transpHAdj g r l (λ x → sym (e x)))))

PostCompEquiv : ∀ {ℓ κ κ'} {A : Type ℓ} {B : A → Type κ} {C : A → Type κ'}
                → (f : (x : A) → B x → C x) → ((x : A) → isEquiv (f x))
                → isEquiv {A = (x : A) → B x} 
                          {B = (x : A) → C x}
                          (λ g x → f x (g x))
PostCompEquiv f ef = 
    ( ( (λ g x → fst (fst (ef x)) (g x))
      , λ g → funext (λ x → snd (fst (ef x)) (g x))))
    , ( (λ g x → fst (snd (ef x)) (g x)) 
      , λ g → funext (λ x → snd (snd (ef x)) (g x)))
```