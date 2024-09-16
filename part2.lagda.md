```agda
{-# OPTIONS --without-K --rewriting #-}
module part2 where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import part1
```

# Polynomials in HoTT

## Basics

**Remark:** for the sake of concision, since essentially all of the categorical structures treated in this paper will be infinite-dimensional, we shall generally omit the prefix "$\infty$-" from our descriptions these structures. Hence hereafter "category" generally means $\infty$-category, "functor" means $\infty$-functor, etc.

Let $\mathbf{Type}$ be the category of types and functions between them. Given a type `A`, let $y^A$ denote the corresponding representable functor $\mathbf{Type} \to \mathbf{Type}$.

A *polynomial functor* is a coproduct of representable functors $\mathbf{Type} \to \mathbf{Type}$, i.e. an endofunctor on $\mathbf{Type}$ of the form $$
\sum_{a : A} y^{B(a)}
$$ for some type `A` and family of types `B : A → Type`. The data of a polynomial functor is thus uniquely determined by the choice of `A` and `B`. Hence we may represent such functors in Agda simply as pairs (A , B) of this form:

```agda
Poly : (ℓ κ : Level) → Type ((lsuc ℓ) ⊔ (lsuc κ))
Poly ℓ κ = Σ (Set ℓ) (λ A → A → Set κ)
```

A basic example of such a polynomial functor is the identity functor `𝕪` consisting of a single term of unit arity – hence represented by the pair `(⊤ , λ _ → ⊤)`.

```agda
𝕪 : Poly lzero lzero
𝕪 = (⊤ , λ _ → ⊤)
```

The observant reader may note the striking similarity of the above-given formula for a polynomial functor and the endofunctor on $\mathbf{Set}^{\mathcal{C}^{op}}$ defined in the previous section on natural models. Indeed, this is no accident, given a type `𝓤` and a function `u : 𝓤 → Type` corresponding to a natural model as described previously, we obtain the corresponding polynomial `𝔲 : Poly` as the pair `(𝓤 , u)`. Hence we can study the structure of `𝓤` and `u` in terms of `𝔲`, and this, as we shall see, allows for some significant simplifications in the theory of natural models.

Given polynomial functors $p = \sum_{a : A} y^{B(a)}$ and $q = \sum_{c : C} y^{D(c)}$, a natural transformation $p \Rightarrow q$ is equivalently given by the data of a *forward* map `f : A → B` and a *backward* map `g : (a : A) → D (f a) → B a`, as can be seen from the following argument via Yoneda: $$
\begin{array}{rl}
& \int_{y \in \mathbf{Type}} \left( \sum_{a : A} y^{B(a)}  \right) \to \sum_{c : C} y^{D(c)}\\
\simeq & \prod_{a : A} \int_{y \in \mathbf{Type}} y^{B(a)} \to \sum_{c : C} y^{D(c)}\\
\simeq & \prod_{a : A} \sum_{c : C} B(a)^{D(c)}\\
\simeq & \sum_{f : A \to C} \prod_{a : A} B(a)^{D(f(c))}
\end{array}
$$ We use the notation $p \leftrightarrows q$ to denote the type of natural transformations from $p$ to $q$ (aka *lenses* from $p$ to $q$), which may be written in Agda as follows:

```agda
_⇆_ : ∀ {ℓ ℓ' κ κ'} → Poly ℓ κ → Poly ℓ' κ' → Type (ℓ ⊔ ℓ' ⊔ κ ⊔ κ')
(A , B) ⇆ (C , D) = Σ (A → C) (λ f → (a : A) → D (f a) → B a)
```

By application of function extensionality, we derive the following type for proofs of equality between lenses: 

```agda
EqLens : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
         → (p ⇆ q) → (p ⇆ q) → Set (ℓ ⊔ ℓ' ⊔ κ ⊔ κ')
EqLens (A , B) (C , D) (f , g) (f' , g') = 
  (a : A) → Σ (f a ≡ f' a) 
              (λ e → (b : D (f a)) → g a b ≡ g' a (transp D e b))
```

For each polynomial $p$, the correspnding *identity* lens is given by the following data:

```agda
id : ∀ {ℓ κ} (p : Poly ℓ κ) → p ⇆ p
id p = ( (λ a → a) , λ a b → b )
```

And given lenses $p \leftrightarrows q$ and $q \leftrightarrows r$, their composition may be computed as follows:

```agda
comp : ∀ {ℓ ℓ' ℓ'' κ κ' κ''} 
       → (p : Poly ℓ κ) (q : Poly ℓ' κ') (r : Poly ℓ'' κ'')
       → p ⇆ q → q ⇆ r → p ⇆ r 
comp p q r (f , g) (h , k) = 
    ( (λ a → h (f a)) , λ a z → g a (k (f a) z) )
```

Hence we have a category $\mathbf{Poly}$ of polynomial functors and lenses between them. Our goal, then, is to show how the type-theoretic structure of a natural model naturally arises from the structure of this category. In fact, $\mathbf{Poly}$ is replete with categorical structures of all kinds, of which we now mention but a few:

## The Vertical-Cartesian Factorization System on $\mathbf{Poly}$

We say that a lens `(f , f♯) : (A , B) ⇆ (C , D)` is *vertical* if `f : A → C` is an equivalence, and Cartesian if for every `a : A`, the map `f♯ a : D[f a] → B a` is an equivalence.

```agda
isVertical : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
             → p ⇆ q → Set (ℓ ⊔ ℓ')
isVertical p q (f , f♯) = isEquiv f

isCartesian : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
             → p ⇆ q → Set (ℓ ⊔ κ ⊔ κ')
isCartesian (A , B) q (f , f♯) = (a : A) → isEquiv (f♯ a)
```

Every lens `(A , B) ⇆ (C , D)` can then be factored as a vertical lens followed by a Cartesian lens:

```agda
vertfactor : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
             → (f : p ⇆ q) → p ⇆ (fst p , λ x → snd q (fst f x))
vertfactor p q (f , f♯) = (λ x → x) , (λ a x → f♯ a x)

vertfactorIsVert : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) 
                   → (q : Poly ℓ' κ') (f : p ⇆ q) 
                   → isVertical p (fst p , λ x → snd q (fst f x))
                                (vertfactor p q f)
vertfactorIsVert p q f = idIsEquiv

cartfactor : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
             → (f : p ⇆ q) → (fst p , λ x → snd q (fst f x)) ⇆ q
cartfactor p q (f , f♯) = f , λ a x → x

cartfactorIsCart : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) 
                   → (q : Poly ℓ' κ') (f : p ⇆ q) 
                   → isCartesian (fst p , λ x → snd q (fst f x)) q
                                 (cartfactor p q f)
cartfactorIsCart p q f x = idIsEquiv

vertcartfactor≡ : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) 
                  → (q : Poly ℓ' κ') (f : p ⇆ q)
                  → EqLens p q f
                           (comp p (fst p , λ x → snd q (fst f x)) q
                                 (vertfactor p q f)
                                 (cartfactor p q f))
vertcartfactor≡ p q f a = refl , (λ b → refl)
```

Of these two classes of morphisms in $\mathbf{Poly}$, it is *Cartesian* lenses that shall be of principal interest to us. If we view a polynomial `p = (A , B)` as an `A`-indexed family of types, given by `B`, then given a lens `(f , f♯) : p ⇆ 𝔲`, we can think of the map `f♯ a : u (f a) → B a`, as an *elimination form* for the type `u (f a)`, i.e. a way of *using* elements of the type `u (f a)`. If we then ask that `(f , f♯)` isCartesian, this implies that the type `u (f a)` is completely characterized (up to equivalence) by this elimination form, and in this sense, `𝔲` *contains* the type `B a`, for all `a : A`.[^3]

[^3]: Those familiar with type theory may recognize this practice of defining types in terms of their elimination forms as characteristic of so-called *negative* types (in opposition to *positive* types, which are characterized by their introduction forms). Indeed, there are good reasons for this, having to do with the fact that negative types are equivalently those whose universal property is given by a *representable* functor, rather than a *co-representable* functor, which reflects the fact that natural models are defined in terms of *presheaves* on a category of contexts, rather than *co-presheaves.*

We can therefore use Cartesian lenses to detect which types are contained in a natural model `𝔲`.

A further fact about Cartesian lenses is that they are closed under identity and composition, as a direct consequence of the closure of equivalences under identity and composition:

```agda
idCart : ∀ {ℓ κ} (p : Poly ℓ κ)
         → isCartesian p p (id p)
idCart p a = idIsEquiv

compCartesian : ∀ {ℓ ℓ' ℓ'' κ κ' κ''}
                → (p : Poly ℓ κ) (q : Poly ℓ' κ') (r : Poly ℓ'' κ'')
                → (f : p ⇆ q) (g : q ⇆ r)
                → isCartesian p q f → isCartesian q r g 
                → isCartesian p r (comp p q r f g)
compCartesian p q r f g cf cg a = 
    compIsEquiv (snd f a) (snd g (fst f a)) (cf a) (cg (fst f a))
```

Hence there is a category $\mathbf{Poly^{Cart}}$ defined as the wide subcategory of $\mathbf{Poly}$ whose morphisms are precisely Cartesian lenses. As we shall see, much of the categorical structure of natural models qua polynomial functors can be derived from the subtle interplay between $\mathbf{Poly^{Cart}}$ and $\mathbf{Poly}$.

### Epi-Mono Factorization on $\mathbf{Poly^{Cart}}$

In fact, $\mathbf{Poly^{Cart}}$ itself inherits a factorization system from the epi-mono factorization on types considered previously.

Define a Cartesian lens `(f , f♯) : p ⇆ q` to be a *Cartesian embedding* if `f` is a monomorphism, and a *Cartesian surjection* if `f` is an epimorphism.

```agda
isCartesianEmbedding : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
                       → (f : p ⇆ q) → isCartesian p q f → Set (ℓ ⊔ ℓ')
isCartesianEmbedding p q (f , f♯) cf = isMono f

isCartesianSurjection : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
                        → (f : p ⇆ q) → isCartesian p q f → Set ℓ'
isCartesianSurjection p q (f , f♯) cf = isEpi f
```

Then every Cartesian lens can be factored into a Cartesian surjection followed by a Cartesian embedding.

```agda
factorcart1 : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
              → (f : p ⇆ q) → isCartesian p q f
              → p ⇆ (Im (fst f) , λ (x , _) → snd q x)
factorcart1 p q (f , f♯) cf = 
    (factor1 f) , f♯

factorcart1IsCart : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
                    → (f : p ⇆ q) (cf : isCartesian p q f)
                    → isCartesian p 
                                  (Im (fst f) , λ (x , _) → snd q x)
                                  (factorcart1 p q f cf)
factorcart1IsCart p q (f , f♯) cf = cf

factorcart1IsEpi : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
                   → (f : p ⇆ q) (cf : isCartesian p q f)
                   → isCartesianSurjection p 
                        (Im (fst f) , λ (x , _) → snd q x)
                        (factorcart1 p q f cf)
                        (factorcart1IsCart p q f cf)
factorcart1IsEpi p q (f , f♯) cf = factor1IsEpi f

factorcart2 : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
              → (f : p ⇆ q) → isCartesian p q f
              → (Im (fst f) , λ (x , _) → snd q x) ⇆ q
factorcart2 p q (f , f♯) cf = (factor2 f) , λ (x , _) y → y

factorcart2IsCart : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
                    → (f : p ⇆ q) (cf : isCartesian p q f)
                    → isCartesian (Im (fst f) , λ (x , _) → snd q x) q
                                  (factorcart2 p q f cf)
factorcart2IsCart p q (f , f♯) cf x = idIsEquiv

factorcart2IsMono : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
                    → (f : p ⇆ q) (cf : isCartesian p q f)
                    → isCartesianEmbedding
                        (Im (fst f) , λ (x , _) → snd q x) q
                        (factorcart2 p q f cf)
                        (factorcart2IsCart p q f cf)
factorcart2IsMono p q (f , f♯) cf = factor2IsMono f

factorcart≡ : ∀ {ℓ ℓ' κ κ'} (p : Poly ℓ κ) (q : Poly ℓ' κ')
              → (f : p ⇆ q) (cf : isCartesian p q f)
              → EqLens p q f
                       (comp p (Im (fst f) , λ (x , _) → snd q x) q
                             (factorcart1 p q f cf)
                             (factorcart2 p q f cf))
factorcart≡ p q f cf x = refl , λ y → refl
```

## Composition of Polynomial Functors

As endofunctors on $\mathbf{Type}$, polynomial functors may straightforwardly be composed. To show that the resulting composite is itself (equivalent to) a polynomial functor, we can reason via the following chain of equivalences: given polynomials `(A , B)` and `(C , D)`, their composite, evaluated at a type `y` is $$
\begin{array}{rl}
& \sum_{a : A} \prod_{b : B(a)} \sum_{c : C} y^{D(c)}\\
\simeq & \sum_{a : A} \sum_{f : B(a) \to C} \prod_{b : B(a)} y^{D(f(b))}\\
\simeq & \sum_{(a , f) : \sum_{a : A} C^{B(a)}} y^{\sum_{b : B(a)} D(f(b))}
\end{array}
$$ This then defines a monoidal product $◃$ on $\mathbf{Poly}$ with monoidal unit given by the identity functor `𝕪`:

```agda
_◃_ : ∀ {ℓ ℓ' κ κ'} → Poly ℓ κ → Poly ℓ' κ' → Poly (ℓ ⊔ κ ⊔ ℓ') (κ ⊔ κ')
(A , B) ◃ (C , D) = (Σ A (λ a → B a → C) , λ (a , f) → Σ (B a) (λ b → D (f b)))

◃Lens : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
        → (p : Poly ℓ κ) (p' : Poly ℓ' κ') 
        → (q : Poly ℓ'' κ'') (q' : Poly ℓ''' κ''')
        → p ⇆ p' → q ⇆ q' → (p ◃ q) ⇆ (p' ◃ q')
◃Lens p p' q q' (f , g) (h , k) =
    ((λ (a , c) → (f a , λ b' → h (c (g a b'))))
    , λ (a , c) (b' , d') → ((g a b') , k (c (g a b')) d'))
```

where `◃Lens` is the action of `◃` on lenses.

By construction, the existence of a Cartesian lens `(σ , σ♯) : 𝔲 ◃ 𝔲 ⇆ 𝔲` effectively shows that `𝔲` is closed under `Σ`-types, since:

* `σ` maps a pair (A , B) consisting of `A : 𝓤` and `B : (u A) → 𝓤` to a term `σ(A,B)` representing the `Σ` type. This corresponds to the type formation rule $$ \inferrule{\Gamma \vdash A : \mathsf{Type}\\ \Gamma, x : A \vdash B[x] ~ \mathsf{Type}}{\Gamma \vdash \Sigma x : A . B[x] ~ \mathsf{Type}} $$
* For all `(A , B)` as above, `σ♯ (A , B)` takes a term of type `σ (A , B)` and yields a term `fst (σ♯ (A , B)) : A` along with a term `snd (σ♯ (A , B)) : B (fst (σ♯ (A , B)))`, corresponding to the elimination rules $$
\inferrule{\Gamma \vdash p : \Sigma x : A . B[x]}{\Gamma \vdash \pi_1(p) : A} \quad \inferrule{\Gamma \vdash p : \Sigma x : A . B[x]}{\Gamma \vdash \pi_2(p) : B[\pi_1(p)]} $$
* The fact that `σ♯ (A , B)` has is an equivalence implies it has an inverse `σ♯⁻¹ (A , B) : Σ (u A) (λ x → u (B x)) → u (σ (A , B))`, which takes a pair of terms to a term of the corresponding pair type, and thus corresponds to the introduction rule $$ \inferrule{\Gamma \vdash a : A\\ \Gamma \vdash b : B[a]}{\Gamma \vdash (a , b) : \Sigma x : A . B[x]} $$
* The fact that $σ♯⁻¹ (A , B)$ is both a left and a right inverse to $σ♯$ then implies the usual $β$ and $η$ laws for dependent pair types $$ \pi_1(a , b) = a \quad \pi_2(a , b) = b \quad p = (\pi_1(p) , \pi_2(p)) $$

Similarly, the existence of a Cartesian lens $(η , η♯) : 𝕪 ⇆ 𝔲$ implies that $𝔲$ contains (a type equivalent to) the unit type, in that:

* There is an element `η tt : 𝓤` which represents the unit type. This corresponds to the type formation rule $$ \inferrule{~}{\Gamma \vdash \top : \mathsf{Type}}$$
* The "elimination rule" `η♯ tt : u(η tt) → ⊤`, applied to an element `x : u(η tt)` is trivial, in that it simply discards `x`. This corresponds to the fact that, in the ordinary type-theoretic presentation, $\top$ does not have an elimination rule.
* However, since this trivial elimination rule has an inverse `η♯⁻¹ tt : ⊤ → u (η tt)`, it follows that there is a (unique) element `η♯⁻¹ tt tt : u (η tt)`, which corresponds to the introduction rule for $\top$: $$\inferrule{~}{\Gamma \vdash \mathsf{tt} : \top}$$
* Moreover, the uniqueness of this element corresponds to the $\eta$-law for $\top$: $$\frac{\Gamma \vdash x : \top}{\Gamma \vdash x = \mathsf{tt}}$$

But then, what sorts of laws can we expect Cartesian lenses as above to obey, and is the existence of such a lens all that is needed to ensure that the natural model $𝔲$ has dependent pair types in the original sense of Awodey & Newstead's definition in terms of Cartesian (pseudo)monads, or is some further data required? And what about `Π` types, or other type formers? To answer these questions, we will need to study the structure of `◃`, along with some closely related functors, in a bit more detail. In particular, we shall see that the structure of `◃` as a monoidal product on $\mathbf{Poly}$ reflects many of the basic identities one expects to hold of `Σ` types.

For instance, the associativity of `◃` corresponds to the associativity of `Σ`-types,

```agda
◃assoc : ∀ {ℓ ℓ' ℓ'' κ κ' κ''}
         → (p : Poly ℓ κ) (q : Poly ℓ' κ') (r : Poly ℓ'' κ'')
         → ((p ◃ q) ◃ r) ⇆ (p ◃ (q ◃ r))
◃assoc p q r = 
    ((λ ((a , f) , g) → (a , (λ b → (f b , λ d → g (b , d))))) 
    , λ ((a , f) , g) (b , (d , x)) → ((b , d) , x))

◃assocCart : ∀ {ℓ ℓ' ℓ'' κ κ' κ''}
             → (p : Poly ℓ κ) (q : Poly ℓ' κ') (r : Poly ℓ'' κ'')
             → isCartesian ((p ◃ q) ◃ r) (p ◃ (q ◃ r)) (◃assoc p q r)
◃assocCart p q r (a , f) = 
    Iso→isEquiv ( (λ ((b , d) , x) → b , d , x)
                , ( (λ (b , d , x) → refl) 
                  , λ ((b , d) , x) → refl))
```

while the left and right unitors of `◃` correspond to the fact that `⊤` is both a left and a right unit for `Σ`-types.

```agda
◃unitl : ∀ {ℓ κ} (p : Poly ℓ κ) → (𝕪 ◃ p) ⇆ p
◃unitl p = (λ (tt , a) → a tt) , λ (tt , a) x → tt , x

◃unitlCart : ∀ {ℓ κ} (p : Poly ℓ κ) 
             → isCartesian (𝕪 ◃ p) p (◃unitl p)
◃unitlCart p (tt , a) = 
    Iso→isEquiv ( (λ (tt , b) → b) 
                , (λ b' → refl) 
                , (λ b' → refl) )

◃unitr : ∀ {ℓ κ} (p : Poly ℓ κ) → (p ◃ 𝕪) ⇆ p
◃unitr p = (λ (a , f) → a) , λ (a , f) b → b , tt

◃unitrCart : ∀ {ℓ κ} (p : Poly ℓ κ) 
             → isCartesian (p ◃ 𝕪) p (◃unitr p)
◃unitrCart p (a , f) =
    Iso→isEquiv ( (λ (b , tt) → b) 
                , (λ b → refl) 
                , (λ (b , tt) → refl) )
```

In fact, `◃` restricts to a monoidal product on $\mathbf{Poly^{Cart}}$, since the functorial action of `◃` on lenses preserves Cartesian lenses:

```agda
◃LensCart : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
            → (p : Poly ℓ κ) (q : Poly ℓ' κ')
            → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
            → (f : p ⇆ q) (g : r ⇆ s)
            → isCartesian p q f → isCartesian r s g
            → isCartesian (p ◃ r) (q ◃ s)
                          (◃Lens p q r s f g)
◃LensCart p q r s (f , f♯) (g , g♯) cf cg (a , h) = 
    pairEquiv (f♯ a) (λ x → g♯ (h (f♯ a x))) 
              (cf a) (λ x → cg (h (f♯ a x)))
```

We should expect, then, for these equivalences to be somehow reflected in the structure of a Cartesian lenses `η : 𝕪 ⇆ 𝔲` and `μ : 𝔲 ◃ 𝔲 ⇆ 𝔲`. This would be the case, e.g., if the following diagrams in $\mathbf{Poly^{Cart}}$ were to commute $$
\begin{tikzcd}
	{y \triangleleft \mathfrak{u}} & {\mathfrak{u} \triangleleft \mathfrak{u} } & {\mathfrak{u} \triangleleft y} \\
	& {\mathfrak{u}}
	\arrow["{\eta \triangleleft \mathfrak{u}}", from=1-1, to=1-2]
	\arrow["{\mathsf{\triangleleft unitl}}"{description}, from=1-1, to=2-2]
	\arrow["\mu", from=1-2, to=2-2]
	\arrow["{\mathfrak{u} \triangleleft \eta}"', from=1-3, to=1-2]
	\arrow["{\mathsf{\triangleleft unitr}}"{description}, from=1-3, to=2-2]
\end{tikzcd} \qquad \begin{tikzcd}
	{(\mathfrak{u} \triangleleft \mathfrak{u}) \triangleleft \mathfrak{u}} & {\mathfrak{u} \triangleleft (\mathfrak{u} \triangleleft \mathfrak{u})} & {\mathfrak{u} \triangleleft \mathfrak{u}} \\
	{\mathfrak{u} \triangleleft \mathfrak{u}} && {\mathfrak{u}}
	\arrow["{\mathsf{\triangleleft assoc}}", from=1-1, to=1-2]
	\arrow["{\mu \triangleleft \mathfrak{u}}"', from=1-1, to=2-1]
	\arrow["{\mathfrak{u} \triangleleft \mu}", from=1-2, to=1-3]
	\arrow["\mu", from=1-3, to=2-3]
	\arrow["\mu"', from=2-1, to=2-3]
\end{tikzcd}
$$

One may recognize these as the usual diagrams for a monoid in a monoidal category, hence (since `◃` corresponds to composition of polynomial endofunctors) for a *monad* as typically defined. However, because of the higher-categorical structure of types in HoTT, we should not only ask for these diagrams to commute, but for the cells exhibiting that these diagrams commute to themselves be subject to higher coherences, and so on, giving `𝔲` not the structure of a (Cartesian) monad, but rather of a (Cartesian) *$\infty$-monad*.

Yet demonstrating that $𝔲$ is an $\infty$-monad involves specifying a potentially infinite amount of coherence data. Have we therefore traded both the Scylla of equality-up-to-isomorphism and the Charybdis of strictness for an even worse fate of higher coherence hell? The answer to this question, surprisingly, is negative, as there is a way to implicitly derive all of this data from a single axiom, which corresponds to the characteristic axiom of HoTT itself: univalence. To show this, we now introduce the central concept of this paper – that of a *polynomial universe*.