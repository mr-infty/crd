import itertools
from itertools import chain 
from sage.modules.free_module_morphism import FreeModuleMorphism
from sage.modules.free_module import FreeModule, FreeModule_generic
from sage.groups.abelian_gps.abelian_group import AbelianGroup
from sage.all import vector, matrix, divisors, GF, Hom, ZZ, QQ
from DeConciniSalvetti import *

def finite_direct_sum_of_constant_family(I, R, M):
    '''Given a finite set I, and a FreeModule M over a ring R, returns the copower M^{(I)} = \bigoplus_{i \in I} M.
    
    More precisely, returns a triple (N, components, from_components), where
       N - instance of FreeModule
       components - function that given an element n of N, returns a dict { i: i-th component of m }
       from_components - function that given a dict { i: n[i] }, returns an element n of N such that n[i] is the i-th component of N
    '''
    assert isinstance(M, FreeModule_generic)
    m = len(M.gens())
    assert m == M.rank()
    index_to_I = list(I)
    len_I = len(index_to_I)
    N = FreeModule(R, len_I*m)
    I_to_index = {}
    for k in range(len_I):
        I_to_index[index_to_I[k]] = k
    def components(x):
        return { i : M.linear_combination_of_basis(x[m*I_to_index[i]:m*(I_to_index[i]+1)]) for i in I }
    def from_components(comp):
        return N.linear_combination_of_basis(list(chain.from_iterable(( M.coordinate_vector(comp[i]) if i in comp.keys() else M.zero_vector() for i in I))))
    return (N, components, from_components)

# M should be a free (combinatorial ?) R[G]-module and N should be a FreeModule over a PID R (must be = ZZ) at the moment
# and action is a function of two variables that given (g, x) as input, where g is an element of G
# and x in an element of N, returns another element of N.
# More precisely: x in an element of N.V(), and given any two elements x,x' of N.V() that define the same element of N,
# i.e. such that x-x' lies in N.W(), the elements action(g,x) and action(g,x') should define the same element of N
def hom_module(M, N, action):
    M_gens = M.gens()
    M_basis = M.basis()
    M_basis_keys = M_basis.keys()
    hom_M_N, components, from_components = finite_direct_sum_of_constant_family(M_basis_keys, N.base_ring(), N)
    def new_action(g, x):
        comp = components(x)
        return from_components({ i: action(g,comp[i]) for i in M_basis_keys })
    return (hom_M_N, M_basis, M_basis_keys, components, from_components, new_action)

def sum_in_module(M, iterable):
    x = M.zero()
    for val in iterable:
        x = x+val
    return x

# Given an action of a monoid on a module,
# this computes the linearly extended action
def linearly_extended_action(M, action, a, x):
    return sum_in_module(M, map(lambda g: a[g]*action(g, x), a.support()))

# Given f: M' --> M, computes the induced homomorphism
#     f^\ast: Hom(M, N) ---> Hom(M', N)
# not very elegant to make this function take hom_M_prime_N_data and hom_M_N_data as additional arguments
# , but I want to avoid unnecessary computations and the problem of nonunique representations, i.e. we shouldn't rely
# on hom_module returning the same objects given the same input.
def hom_module_induced_morphism(f, N, action, hom_M_prime_N_data, hom_M_N_data):
    M_prime = f.domain()
    M = f.codomain()
    hom_M_prime_N, M_prime_basis, M_prime_basis_keys, prime_components, prime_from_components, prime_hom_action = hom_M_prime_N_data
    hom_M_N, M_basis, M_basis_keys, components, from_components, hom_action = hom_M_N_data
    f_values = {}
    for i_prime in M_prime_basis_keys:
        f_values[i_prime] = f(M_prime_basis[i_prime])
    def f_star_components(x):
        c_x = components(x)
        c = {}
        for i_prime in M_prime_basis_keys:
            a = f_values[i_prime]
            for c in N.coordinates(sum_in_module(N, [ linearly_extended_action(N, action, a[i], c_x[i]) for i in a.support() ])):
                yield c
    matrix_representing_f_star = matrix([tuple(f_star_components(x)) for x in hom_M_N.basis()], ncols=hom_M_prime_N.rank())
    return FreeModuleMorphism(Hom(hom_M_N, hom_M_prime_N), matrix_representing_f_star)

def coroot_lattice_as_fg_Z_W_module(cartan_type):
    R = RootSystem(cartan_type)
    L = R.coroot_lattice()
    basis = L.basis()
    basis_keys = basis.keys()
    M = FreeModule(ZZ, len(basis_keys)) # Instances of CombinatorialFreeModule aren't instances of FreeModule: WTF?!?
    W = L.weyl_group()
    def M_to_L(x):
        d = x.dict()
        return sum_in_module(L, [ d[i]*basis[basis_keys[i]] for i in d.keys() ])
    def L_to_M(x): # this is slows a hell!
        return vector(list([ x[k] for k in basis_keys ]))
    def new_action(g, x): # TODO this is slow, *really*, *really* slow. Fix this!
        return L_to_M(g.action(M_to_L(x)))
    return (W, L, M, M_to_L, L_to_M, new_action)

# given a FreeModule M over a ring R' with a coerce_map to R,
# returns the base change of M to R, i.e. M\otimes_{R'} R
def base_change_module(M,R):
    assert R.has_coerce_map_from(M.base_ring())
    MM = FreeModule(R, len(M.basis()))
    # given an element x of M, returns the image of x in MM under the canonical map
    # M ---> MM = M \otimes_{R'} R
    def base_change_map(x):
        return MM.from_vector(vector(map(R.coerce_map_from(M.base_ring()), M.coordinates(x))))
    MM.base_change_map = base_change_map
    return MM

# given a f homomorphism between FreeModule's over a ring R' that is
# endowed with a coerce map to a ring R, returns the base change of f:
#     f\otimes_{R'} R: M\otimes_{R'} R ---> N\otimes_{R'} R
def base_change_morphism(f, R):
    M = f.domain()
    N = f.codomain()
    assert R.has_coerce_map_from(f.base_ring())
    MM = base_change_module(M, R)
    NN = base_change_module(N, R)
    return FreeModuleMorphism(Hom(MM,NN), f.matrix().change_ring(R))

# class generating the lattices Q(R^vee) <= X_\Omega <= P(R^vee)
# , corresponding to subgroups \Omega <= P(R^vee)/Q(R^vee), as
# free ZZ-modules endowed with action of the Weyl Group
# 
# TODO: At the moment, only the computation of the cocharacter lattice is implemented,
# as it's the only thing we need. Maybe one fine day I shall implement the character lattice
# too.
class RootDatumGenerator:
    def __init__(self, R):
        self.R = R # don't really need to keep this, but might as well
        self.Pvee = R.coweight_lattice()
        basis = self.Pvee.basis()
        basis_keys = tuple(basis.keys())
        dim = len(basis_keys)
        self.MPvee = FreeModule(ZZ, dim)
        self.MQvee = self.MPvee.submodule([ vector([ alpha_vee[j] for j in basis_keys ]) for alpha_vee in self.Pvee.simple_roots() ])
        self.fundamental_group = self.MPvee/self.MQvee
        def Pvee_to_MPvee(x):
            return vector([ x[k] for k in basis_keys ]) # using x[k] is way faster than x.coefficient(k)
        def MPvee_to_Pvee(x):
            return sum_in_module(self.Pvee, [ x[i]*basis[basis_keys[i]] for i in range(dim) ])
        def action52(g, x):
            return Pvee_to_MPvee(g.action(MPvee_to_Pvee(x)))
        self.action = action52
        self.Pvee_to_MPvee = Pvee_to_MPvee
        self.MPvee_to_Pvee = MPvee_to_Pvee

    # returns an element of Pvee that maps to x under Pvee -->> fundamental_group
    def lift_to_Pvee(self, x):
        return self.MPvee_to_Pvee(x.lift())

    # returns the image of the element x under the map Pvee -->> fundamental_group
    def map_to_fundamental_group(self, x):
        return self.Pvee_to_MPvee(x)

    # returns the sublattice X of Pvee corresponding to the subgroup Omega of the fundamental_group
    def cocharacter_lattice(self, Omega):
        return self.MPvee.submodule(list(self.MQvee.gens()) + [ x.lift() for x in Omega.gens() ])

class CohomologyOfRootData(RootDatumGenerator):
    def __init__(self, R):
        RootDatumGenerator.__init__(self, R)
        self.W = R.coweight_lattice().weyl_group()

    def cohomology_of_cocharacter_lattice(self, Omega):
        WC = WeylCohomology(self.W, self.cocharacter_lattice(Omega), self.action)
        WC_mod2, comparison = WC.base_change(GF(2))
        def universal_2_cocycle():
            assert tuple(self.W.simple_reflections().keys()) == tuple(self.Pvee.simple_roots().keys())
            assert list(self.W.simple_reflections().keys()) == list(self.Pvee.basis().keys())
            indices = self.W.simple_reflections().keys()
            assert all(self.W.simple_reflections()[i].action(self.Pvee.simple_roots()[i]) == -self.Pvee.simple_roots()[i] for i in indices) # make sure numberings match up
            K2, K2_basis, K2_basis_keys, K2_components, K2_from_components, K2_action = WC._K(2)
            phi_u_components = {}
            for i in indices:
                Gamma = ((i,), (i,))
                assert Gamma in K2_basis_keys
                phi_u_components[Gamma] = self.Pvee.simple_roots()[i] # again, L.simple_roots() actually consists of coroots (weird convention)
            return K2_from_components({Gamma: self.Pvee_to_MPvee(phi_u_components[Gamma]) for Gamma in phi_u_components.keys()})
        phi_u = WC_mod2.K(2).base_change_map(universal_2_cocycle()) # universal_2_cocycle() lives in Hom(CS_2, X^vee) (and isn't actually a cocycle)
        _comp = {}
        def comparison_on_gens(k):
            if not k in _comp:
                _comp[k] = [ WC_mod2.H(k).quotient_map()(WC_mod2.K(k).base_change_map(x.lift())) for x in WC.H(k).gens() ]
            return _comp[k]
        mod2_ker = WC_mod2.d(2).kernel()
        M = mod2_ker / mod2_ker.submodule([ WC_mod2.K(2).base_change_map(x) for x in WC.d(2).kernel().gens() ])
        return (WC, WC_mod2, comparison_on_gens, phi_u, WC_mod2.H(2).quotient_map()(phi_u), M.quotient_map()(phi_u))

def subgroups_of_finite_abelian_group(A):
    assert len(A.invariants()) == len(A.gens())
    B = AbelianGroup(A.invariants()) # A is an instance of FGP_Module, which is not a subclass of AbelianGroup
    # The Sage function AbelianGroup.subgroups is *really, really* slow (as of version 8.1)
    for BB in reversed(B.subgroups()): # I prefer to get smaller subgroups first
        yield A.submodule([ A.sum(( gen.exponents()[i]*A.gens()[i] for i in range(len(A.gens())) )) for gen in BB.gens() ])

def faster_kernel(f):
    '''Computes the kernel of a morphism between FreeModules.

    Until this is fixed in Sage, it is necessary if we want to compute
    kernels of integer matrices in our lifetime.
    '''
    if f.base_ring() == ZZ:
        K = f.matrix().change_ring(QQ).kernel().intersection(FreeModule(ZZ, f.domain().rank()))
        return f.domain().submodule([ f.domain().linear_combination_of_basis(x) for x in K.gens() ])
    else:
        return f.kernel()

# base class for cocomplexes that are dimension-wise finite free R-modules
class CocomplexOfFreeModules:
    def __init__(self, R=ZZ):
        self.R = R

    def base_ring(self):
        return self.R

    # the k-th dimensional module
    def K(self, k):
        raise NotImplementedError # override in subclass

    # the k-th dimensional differential d(k): K(k) --> K(k+1)
    def d(self, k):
        raise NotImplementedError # override in subclass

    def base_change(self, new_base):
        assert new_base.has_coerce_map_from(self.R) # in a just world, we would start from a ring morphism, and wouldn't need this code
        new_cocomplex = CocomplexOfFreeModules(new_base)
        _K = {}
        _d = {}
        def new_K(new_self, k):
            if not k in _K:
                _K[k] = base_change_module(self.K(k), new_base) # self.K(k).change_ring(new_base)
            return _K[k]
        def new_d(new_self, k):
            if not k in _d:
                _d[k] = base_change_morphism(self.d(k), new_base) # self.d(k).change_ring(new_base)
            return _d[k]
        # comparison map, given k returns a (python) function
        #      self.K(k) --> self.base_change(new_base).K(k)
        # at the moment, this is just the identity (because of Sage's weirdness)
        def comparison(k):
            def identity(x):
                return x
            return identity
        new_cocomplex.K = new_K.__get__(new_cocomplex, CocomplexOfFreeModules) # thanks to Mad Physicist! https://stackoverflow.com/q/394770/
        new_cocomplex.d = new_d.__get__(new_cocomplex, CocomplexOfFreeModules)
        
        return (new_cocomplex, comparison)

    # the k-th dimensional cohomology group
    def H(self, k):
        if not hasattr(self, '_H'):
            self._H = {}
        if not k in self._H:
            self._H[k] = faster_kernel(self.d(k))/self.d(k-1).image()
        return self._H[k]

# A cocomplex K that computes the cohomology of a R[W]-module M.
# More precisely, the cocomplex K(k) = Hom_R[W](C(k),M), where C(k) is 
# the DeConcini-Salvetti resolution of the trivial R[W]-module R.
# 
# It is assumed that R is a principal ideal domain and that M is a FreeModule over R.
class WeylCohomology(CocomplexOfFreeModules):
    def __init__(self, W, M, action, R=ZZ):
        self.DCSR = DeConciniSalvettiResolution(W, R)
        self.M = M
        self.action = action
        self.R = R
        self.modules = {}
        self.differential = {}
        self.cohomology = {}

    def _K(self, k):
        if not k in self.modules:
            self.modules[k] = hom_module(self.DCSR.C(k), self.M, self.action)
        return self.modules[k]

    def K(self, k):
        return self._K(k)[0]

    def d(self, k):
        if not k in self.differential:
            self.differential[k] = hom_module_induced_morphism(self.DCSR.delta(k+1), self.M, self.action, self._K(k+1), self._K(k))
        return self.differential[k]

def test():
    def d(cartan_type):
        CRD = CohomologyOfRootData(RootSystem(cartan_type))
        _, WC_mod2, _, _, _ = CRD.cohomology_of_cocharacter_lattice(CRD.fundamental_group.submodule([]))
        return WC_mod2.H(2).dimension()
    dims = {1: 1,
            2: 0,
            3: 2,
            4: 0,
            5: 3,
            6: 0,
            7: 3,
            8: 0}
    for ell in dims.keys():
        print "Checking that dim_\\F_2 H^2(W_0,X^\\vee \\otimes_\\Z \\F_2) = %d for A_%d" % (dims[ell], ell)
        dim = d(['A',ell])
        if dim == dims[ell]:
            print "OK"
        else:
            print "Test FAILED: dimension = %d" % dim
