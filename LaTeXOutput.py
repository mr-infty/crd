import itertools
from sage.all import *
from CoxeterCohomology import *
from cypari2.handle_error import PariError
from os.path import isfile

def latex_rep_of_finite_abelian_group_with_invariants(invariants):
    if len(invariants) == 0:
        return '0'
    return ' \\oplus '.join(map(lambda n: ('\\Z/%d\\Z' % n) if n > 0 else '\\Z', invariants))

def latex_rep_of_fundamental_group(crd):
    omega = crd.fundamental_group
    return (latex_rep_of_finite_abelian_group_with_invariants(omega.invariants()), ', '.join(map(lambda gen: crd.lift_to_Pvee(gen)._latex_(), omega.gens())))

def latex_rep_of_subgroup_of_fundamental_group(crd, omega_prime):
    if omega_prime == crd.fundamental_group:
        return 'P^\\vee/Q^\\vee'
    s = ', '.join(map(lambda x: str(crd.fundamental_group.coerce_map_from(omega_prime)(x)), omega_prime.gens()))
    if s == '':
        return '0'
    else:
        return '\\left<%s\\right>' % s

def latex_rep_of_salvetti_flag(Gamma):
    return ' \\supseteq '.join(map(lambda Lambda_i: '%s' % ','.join(map(str, Lambda_i)), Gamma))

def latex_rep_of_element_of_Pvee(x):
    return x._latex_()

def latex_rep_of_element_of_MPvee(crd, x):
    return latex_rep_of_element_of_Pvee(crd.MPvee_to_Pvee(x))

def latex_rep_of_element_of_MXvee(crd, MXvee, x):
    return latex_rep_of_element_of_Pvee(crd.MPvee_to_Pvee(crd.MPvee.coerce_map_from(MXvee)(x)))

def latex_rep_of_salvetti_cochain(WC, k, phi, rep_for_M=str):
    """Returns latex representation of the element phi of WC.K(k)."""
    _, M_basis, M_basis_keys, components, _, _ = WC._K(k)
    comp = components(phi)
    def optional_parentheses(x):
        return ('\\left(%s\\right)' % x) if ('+' in x or '-' in x) else x
    s = ' + '.join(map(lambda Gamma: '%s\\bm{\\text{\\mbox{$[%s]$}}}' % (optional_parentheses(rep_for_M(comp[Gamma])), latex_rep_of_salvetti_flag(Gamma)), filter(lambda Gamma: not comp[Gamma].is_zero(), M_basis_keys)))
    return s if not s == '' else '0'

def transpose_matrix(A):
    n = len(A)
    if n == 0:
        return A
    m = len(A[0])
    return [ [ A[j][i] for j in range(n) ] for i in range(m) ]

def latex_rep_of_matrix(A):
    matrix_contents = ''
    for row in A:
        matrix_contents += ' & '.join(map(str, row)) + ' \\\\ '
    return '\\begin{pmatrix} %s \\end{pmatrix}' % (matrix_contents if matrix_contents != '' else '\\relax')

def latex_rep_of_cohomology(omega_prime, crd, WC, WC_mod2, comparison_on_gens, phi_u, class_of_phi_u, class_of_phi_u_mod, range_of_k=[0,1,2,3]):
    s = ''
    def cochain_rep(k, x):
        return latex_rep_of_salvetti_cochain(WC, k, x, rep_for_M=lambda x: latex_rep_of_element_of_MXvee(crd, WC.M, x))
    def mod2_cochain_rep(k, x):
        x_lifted = WC.K(k).linear_combination_of_basis([ GF(2).lift(y) for y in x]) # lift to cochain in the Salvetti complex over MXvee
        return latex_rep_of_salvetti_cochain(WC, k, x_lifted, rep_for_M=lambda x: latex_rep_of_element_of_MXvee(crd, WC.M, x))
    def rep_of_comparison(comparison_on_gens):
        A = [ x.list() for x in comparison_on_gens ]
        return latex_rep_of_matrix(transpose_matrix(A))
    # The cocycle phi_u
    s += '\n\\vskip 5pt'
    s += '\n\\begin{center}'
    s += '\n\\scalebox{1.15}{\\fbox{\\begin{tabu}spread 1cm{X[-1,R,$$]X[-1,L,$$]}'
    if phi_u.is_zero():
        s += '\n \\phi_u & =\\ 0 \\\\'
    elif class_of_phi_u.is_zero():
        s += '\n \\phi_u & =\\ \\partial \\tau \\text{ with } \\tau = %s \\\\' % mod2_cochain_rep(1, WC_mod2.d(1).lift(phi_u))
    else:
        s += '\n [\\phi_u] & =\\ \\left(%s\\right) \\\\' % ', '.join(map(str, WC_mod2.H(2).coordinate_vector(class_of_phi_u)))
        if class_of_phi_u_mod.is_zero():
            s += '\n & \\textbf{ lies in the image of $\\text{comp}_2$}' # TODO: Give pre-image
        else:
            s += '\n & \\textbf{ does not lie in the image of $\\text{comp}_2$}'
    s += '\n\\end{tabu}}}'
    s += '\n\\end{center}\n'
    # Integral cohomology
    s += '\n\\begin{longtabu}{lX[-0.3,C,$$]>{\\footnotesize}X[1,L,$$]}'
    s += '\n\\toprule'
    s += '\n\\rowfont{\\bf}'
    s += '\nk & H^k(W_0, X^\\vee) & \\textbf{{\\normalsize generating cocycles}} \\\\'
    s += '\n\\midrule'
    s += '\n\\endhead'
    row_counter = 1
    n_rows = len(range_of_k)
    for k in range_of_k:
        row = '%d & ' % k
        row += '%s & ' % latex_rep_of_finite_abelian_group_with_invariants(WC.H(k).invariants())
        row += '%s' % ' \\linebreak \\newline '.join(map(lambda x: cochain_rep(k, x.lift()), WC.H(k).gens()))
        s += '\n%s \\\\%s' % (row, '\\\\' if row_counter < n_rows else '')
        row_counter += 1
    s += '\n\\bottomrule'
    s += '\n\\end{longtabu}\n\n\\vskip 0.5cm\n'
    # Mod 2 cohomology
    s += '\n\\begin{longtabu}{lX[0.1,C,$$]>{\\footnotesize}X[1,L,$$]}'
    s += '\n\\toprule'
    s += '\n\\rowfont{\\bf}'
    s += '\nk & h^k(\\overline{X^\\vee}) & \\textbf{{\\normalsize generating cocycles}} \\\\'
    s += '\n\\midrule'
    s += '\n\\endhead'
    row_counter = 1
    for k in range_of_k:
        row = '%d & ' % k
        row += '%s & ' % str(WC_mod2.H(k).dimension())
        row += '%s' % ' \\linebreak \\newline '.join(map(lambda x: mod2_cochain_rep(k, WC_mod2.H(k).lift_map()(x)), WC_mod2.H(k).gens()))
        s += '\n%s \\\\%s' % (row, '\\\\' if row_counter < n_rows else '')
        row_counter += 1
    s += '\n\\bottomrule'
    s += '\n\\end{longtabu}\n\n\\vskip 0.5cm\n'
    # Matrices of comparison maps
    s += '\n\\begin{center}\\begin{tabu}spread 1cm {>{\\bf}X[-1,R,$$]X[-1,C,$$]X[-1,C,$$]X[-1,C,$$]X[-1,C,$$]}'
    s += '\n\\toprule'
    s += '\n%s \\\\' % ' & '.join(('\\textbf{k}',) + tuple(map(str, range_of_k)))
    s += '\n\\midrule'
    s += '\n%s \\\\' % ' & '.join(('\\textbf{comp}_k',) + tuple(map(lambda k: rep_of_comparison(comparison_on_gens(k)), range_of_k)))
    s += '\n\\bottomrule'
    s += '\n\\end{tabu}\\end{center}\n'
    s += '\n\\vskip 1 cm \n'
    return s

def latex_rep_of_trivial_cohomology(crd, WC_triv, WC_triv_mod2, range_of_k=[0,1,2,3]):
    s = ''
    def cochain_rep(WC, k, x):
        return latex_rep_of_salvetti_cochain(WC, k, x, rep_for_M=lambda x: '' if x[0] == 1 else str(x[0]))
    # Trivial integral cohomology
    s += '\n\\begin{longtabu}{lX[0.3,C,$$]>{\\footnotesize}X[1,L,$$]}'
    s += '\n\\toprule'
    s += '\n\\rowfont{\\bf}'
    s += '\nk & H^k(W_0, \\Z) & \\text{{\\normalsize generating cocycles}} \\\\'
    s += '\n\\midrule'
    s += '\n\\endhead'
    row_counter = 1
    n_rows = len(range_of_k)
    for k in range_of_k:
        row = '%d & ' % k
        row += '%s & ' % latex_rep_of_finite_abelian_group_with_invariants(WC_triv.H(k).invariants())
        row += '%s' % ' \\linebreak \\newline '.join(map(lambda x: cochain_rep(WC_triv, k, x.lift()), WC_triv.H(k).gens()))
        s += '\n%s \\\\%s' % (row, '\\\\' if row_counter < n_rows else '')
        row_counter += 1
    s += '\n\\bottomrule'
    s += '\n\\end{longtabu}\n\n\\vskip 0.5cm\n'
    # Trivial Mod 2 cohomology
    s += '\n\\begin{longtabu}{lX[0.1,C,$$]>{\\footnotesize}X[1,L,$$]}'
    s += '\n\\toprule'
    s += '\n\\rowfont{\\bf}'
    s += '\nk & h^k(\\F_2) & \\text{{\\normalsize generating cocycles}} \\\\'
    s += '\n\\midrule'
    s += '\n\\endhead'
    row_counter = 1
    for k in range_of_k:
        row = '%d & ' % k
        row += '%s & ' % str(WC_triv_mod2.H(k).dimension())
        row += '%s' % ' \\linebreak \\newline '.join(map(lambda x: cochain_rep(WC_triv_mod2, k, WC_triv_mod2.H(k).lift_map()(x)), WC_triv_mod2.H(k).gens()))
        s += '\n%s \\\\%s' % (row, '\\\\' if row_counter < n_rows else '')
        row_counter += 1
    s += '\n\\bottomrule'
    s += '\n\\end{longtabu}\n\n\\vskip 1cm \n'
    return s

def latex_rep_of_cohomology_of_type(cartan_type):
    s = ''
    R = RootSystem(cartan_type)
    CRD = CohomologyOfRootData(R)
    cartan_type_text_repr = "%s%d" % (cartan_type[0], cartan_type[1])
    s += '\\subsection{Root system \\texorpdfstring{$%s$}{%s}}' % (R.cartan_type()._latex_(), cartan_type_text_repr)
    s += '\n\\fbox{\\begin{tabular}{rp{1cm}l}'
    s += '\n\\textbf{Dynkin diagram} & & %s \\\\ [2em]' % R.dynkin_diagram()._latex_()
    group_rep, gens_rep = latex_rep_of_fundamental_group(CRD)
    s += '\n\\textbf{Fundamental group} & & \n{$\\begin{aligned} P^\\vee/Q^\\vee & \simeq %s \\\\' % group_rep
    if len(gens_rep) > 0:
        s += '\n & \\text{ generated by } %s \\in P^\\vee \\mod Q^\\vee' % gens_rep
    s += '\n\\end{aligned}$}'
    s += '\n\\end{tabular}}\n'
    section_counter = 0
    for omega in subgroups_of_finite_abelian_group(CRD.fundamental_group):
        WC, WC_mod2, comp_on_gens, phi_u, class_of_phi_u, class_of_phi_u_mod = CRD.cohomology_of_cocharacter_lattice(omega)
        if omega.invariants() == (): # simply connected case
            s += '\n\\subsubsection{Cohomology of coroot lattice \\texorpdfstring{$X^\\vee = Q^\\vee$}{X^v = Q^v}}'
            s += '\n\\label{subsub:cohomology_of_%s_simply_connected}' % cartan_type_text_repr
        elif omega == CRD.fundamental_group: # adjoint case
            s += '\n\\subsubsection{Cohomology of coweight lattice \\texorpdfstring{$X^\\vee = P^\\vee$}{X^v = P^v}}'
            s += '\n\\label{subsub:cohomology_of_%s_adjoint}' % cartan_type_text_repr
        else: # general case
            omega_latex_rep = latex_rep_of_subgroup_of_fundamental_group(CRD, omega)
            omega_text_rep = str(omega)
            s += '\n\\subsubsection{Cohomology of lattice \\texorpdfstring{$X^\\vee$}{X^v} corresponding to \\texorpdfstring{$\\Omega = %s$}{Omega = %s}}' % (omega_latex_rep, omega_text_rep)
            s += '\n\\label{subsub:cohomology_of_%s_%d}' % (cartan_type_text_repr, section_counter)
            section_counter += 1
        s += '\n'+latex_rep_of_cohomology(omega, CRD, WC, WC_mod2, comp_on_gens, phi_u, class_of_phi_u, class_of_phi_u_mod)
    WC_triv = WeylCohomology(CRD.W, FreeModule(ZZ, 1), lambda g,x: x, R=ZZ)
    WC_triv_mod2 = WeylCohomology(CRD.W, FreeModule(GF(2), 1), lambda g,x: x, R=GF(2))
    s += '\n\\subsubsection{Cohomology with trivial coefficients}'
    s += '\n\\label{subsub:cohomology_of_%s_with_trivial_coefficients}' % cartan_type_text_repr
    s += '\n'+latex_rep_of_trivial_cohomology(CRD, WC_triv, WC_triv_mod2)
    return s

def compute_cohomology_for_type(X, range_of_ell):
    for ell in range_of_ell:
        print "Computing cohomology of %s_%d ..." % (X, ell)
        filename = 'cohomology_of_%s_%d.tex' % (X, ell)
        if isfile(filename):
            print "File already exists, SKIPPING."
        else:
            s = latex_rep_of_cohomology_of_type([X,ell])
            with open(filename, 'w') as f:
                f.write(s)
            print "DONE."
