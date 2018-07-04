from itertools import chain
from sage.all import ZZ
from sage.combinat.free_module import CombinatorialFreeModule

def subsets_of_cardinality_atmost(S,k):
    """Returns an iterable of all the subsets of cardinality <= k of the (finite) set S."""
    assert k >= 0
    if k > 0 and len(S) > 0:
        for SS in subsets_of_cardinality_atmost(S[1:], k):
            yield SS
            if len(SS) < k:
                yield (S[0],)+SS
    else:
        yield ()

# TODO: Return only those flags with \Gamma_1 generating a finite subgroup, i.e. such that
# order(st) < \infty for all s,t \in S, in order to support finitely generated infinite Coxeter groups.
def flags_of_cardinality(S,k):
    """Returns an iterable over all the flags of cardinality k over the (finite) set S.
    
    Returns an iterable over all tuples (Gamma_1, Gamma_2, ...) s.t. S \supseteq Gamma_1 \supseteq Gamma_2
    and \sum_{i \geq 1} \# Gamma_i = k
    """
    assert k >= 0
    if k == 0:
        yield ()
    elif len(S) > 0:
        for Gamma_1 in subsets_of_cardinality_atmost(S,k):
            m = len(Gamma_1)
            for flag in flags_of_cardinality(Gamma_1, k-m):
                yield (Gamma_1,) + flag

def minimal_coset_representatives(W, TT, T):
    """Returns the representatives of the left <TT>-cosets in <T>.
    
    Given a Coxeter group W and subsets TT \subseteq T of the set S of distinguished generators of W,
    returns the representatives of the left <TT>-cosets in the subgroups <T> of W.
    """
    reps = [W.one()]
    yield W.one()
    n = 0
    while len(reps) > 0:
        n = n+1
        longer_reps = []
        for g in reps:
            for s in T:
                gg = s*g
                l = gg.length()
                if l == n and not gg in longer_reps and all( (gg*t).length() > l for t in TT ):
                    yield gg
                    longer_reps.append(gg)
        reps = longer_reps

def mu(Gamma, tau):
    """Returns \# { \gamma \in \Gamma : \gamma \leq \tau \}.
    
    Given a set Gamma of integers and an integer tau in Gamma, returns the
    number of elements of Gamma that are smaller or equal to tau.
    """
    return sum(1 for x in Gamma if x <= tau)

def number_of_inversions(f, X):
    return sum(chain.from_iterable((1 for y in X if x < y and f[x] > f[y]) for x in X))

def alpha(W, Gamma, i, tau, beta, conj_map):
    return i*beta.length() + sum(len(Gamma_j) for Gamma_j in Gamma[:i-1]) + mu(Gamma[i-1], tau) + sum(number_of_inversions(conj_map, Gamma_j) for Gamma_j in Gamma[i:])

def compute_conj_map(W, beta, X, Y):
    """Returns the dictionary describing the mapping Gamma_i_plus_one -> Gamma_i_minus_tau, x |-> \beta.inverse() * x * beta if well-defined, otherwise None.

    Given a Coxeter group W and an element beta of W, and sequences X, Y of elements of W.simple_reflections().keys(),
    returns a dictionary f such that
        f[x] = beta.inverse() * x * beta
    for all x in X, if the right hand side is an element of Y for all x, otherwise returns None.
    """
    beta_inv = beta.inverse()
    conj_map = {}
    for x in X:
        gg = beta_inv * W.simple_reflections()[x] * beta
        for y in W.simple_reflections().keys():
            if W.simple_reflections()[y] == gg:
                if y in Y:
                    conj_map[x] = y
                    break
                else:
                    return None
        if not x in conj_map: # beta^(-1) * x * beta isn't even a simple reflection
            return None
    return conj_map

class DeConciniSalvettiResolution:
    """Class representing the free resolution of the trivial R[W]-module R as constructed by DeConcini-Salvetti"""
    def __init__(self, W, R=ZZ):
        """Constructs the DeConcini-Salvetti resolution of W.

        Given a finite Coxeter group W (actually, W can be finitely or even countably generated, but that's not implemented right now),
        returns the DeConcini-Salvetti resolution of the trivial R[W]-module R.
        """
        self.W = W
        self.R = R
        self._modules = {}
        self._flags = {}
        self._morphisms = {}

    def S(self, k):
        """Returns the canonical basis of C(k), given by the set of flags of cardinality k."""
        assert k >= 0
        if not k in self._flags:
            self._flags[k] = list(flags_of_cardinality(self.W.simple_reflections().keys(), k)) # TODO: I'm using the keys instead of the generators themselves; is this necessary?
        return self._flags[k]

    def C(self, k):
        """The k-dimensional piece of the deConcini-Salvetti complex (C(k) = 0 for k < 0)."""
        if not k in self._modules:
            if k >= 0:
                self._modules[k] = CombinatorialFreeModule(self.W.algebra(self.R), self.S(k))
            else:
                self._modules[k] = CombinatorialFreeModule(self.W.algebra(self.R), [])
        return self._modules[k]

    def delta(self, k):
        """The differential delta(k): C(k) -> C(k-1).

        Given an integer k, returns the differential delta(k): C(k) -> C(k-1) in degree k.
        """
        Ck_minus_1_basis = self.C(k-1).basis()
        def index_to_reflection(k):
            return self.W.simple_reflections()[k]
        def delta_terms(Gamma):
            for i in [ i for i in range(len(Gamma)) if len(Gamma[i]) > (len(Gamma[i+1]) if i+1 < len(Gamma) else 0) ]:
                Gamma_i_plus_one = Gamma[i+1] if i+1 < len(Gamma) else ()
                for tau in Gamma[i]:
                    Gamma_i_minus_tau = tuple( x for x in Gamma[i] if not x == tau )
                    for beta in minimal_coset_representatives(self.W, map(index_to_reflection, Gamma_i_minus_tau), map(index_to_reflection, Gamma[i])):
                        beta_inv = beta.inverse()
                        conj_map = compute_conj_map(self.W, beta, Gamma_i_plus_one, Gamma_i_minus_tau)
                        if conj_map == None: # x |-> beta^{-1} * x * beta does not define a map from Gamma_i_plus_one to Gamma_i_minus_tau
                            continue
                        if len(Gamma_i_minus_tau) > 0:
                            Gamma_prime = Gamma[:i] + (Gamma_i_minus_tau,) + tuple(tuple(sorted(conj_map[x] for x in Gamma_j)) for Gamma_j in Gamma[i+1:])
                        else:
                            Gamma_prime = Gamma[:i]
                        yield (-1)**alpha(self.W, Gamma, i+1, tau, beta, conj_map) * (beta * Ck_minus_1_basis[Gamma_prime])

        def delta(Gamma):
            return sum(delta_terms(Gamma))
        if not k in self._morphisms:
            if k >= 1:
                self._morphisms[k] = self.C(k).module_morphism(on_basis=delta, codomain=self.C(k-1))
            else:
                self._morphisms[k] = self.C(k).module_morphism(on_basis=lambda x: self.C(k).zero(), codomain=self.C(k-1))
        return self._morphisms[k]
