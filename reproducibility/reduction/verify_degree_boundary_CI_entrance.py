"""Independent bounded-exception reconstruction for the degree-boundary theorem."""
from pathlib import Path
from itertools import combinations_with_replacement
from math import comb
import json,hashlib,re,sys
from verify_divided_CI_surplus_three_primitive import kernel
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import sub,mul,sign,evaluate
from audit_binary_CI_infinite_padding_entrance import minor
from audit_minimum_staircase_scaled_dyadic import arm_prefix

ROOT=Path(__file__).resolve().parent
ZERO=(0,0);P=(0,1)

def reverse_divided(L,u):
    E=fastconv(L,[comb(u,j) for j in range(u+1)])
    J=[ZERO]*(len(E)-1);following=ZERO
    for n in range(len(E)-1,0,-1):
        J[n-1]=mul(P,sub((E[n],0),following));following=J[n-1]
    assert J[0]==sub((1,0),evaluate(E,(0,-1)))
    return J

def main():
    qa=json.loads((ROOT/'audit_degree_boundary_CI_entrance.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_PASS_DEGREE_BOUNDARY_REFINEMENT_UNDER_PROOF_AUDIT'
    assert qa['state_sha256']=='b7d9ed48acfc91641282473694a2521e848c718af1d9e30f8562db99951720a3'
    names=['quadratic_geometric_decay','quadruple_interior_payment','quadruple_row_zero_payments',
        'quadruple_penultimate_payment','boundary_first_ordinary_minor','boundary_junction_scalar',
        'boundary_interval_junction_gap','boundary_perturbed_junction','single_last_primitive_identity',
        'lower_previous_boundary_preserves_LC','subgolden_entrance_and_one_seed']
    finite_name='DegreeBoundaryCIChunkCertificate'
    produced={(z['u'],tuple(z['V'])):z for z in qa['complete_small_contexts']}
    keys=set();cert=set();startups={};integer_margins=set();comparisons=0
    # Independent grammar: capacity multisets with bounded length, NOT recursive degree partitions.
    for length in range(1,8):
        for V in combinations_with_replacement(range(3,17),length):
            u=sum(t-1 for t in V)
            if not 2<=u<=15:continue
            key=(u,V);keys.add(key);assert produced[key]['exception']==(V==(4,))
            L=[1]
            for t in V:L=fastconv(L,[1]*t)
            J=reverse_divided(L,u)
            assert all(sign(x)>0 for x in J)
            cert.update(J)
            for n in range(1,len(J)-1):cert.add(minor(J,n))
            d=[sub(x,J[n-1] if n else ZERO) for n,x in enumerate(J)]
            dp=[x if sign(x)>0 else ZERO for x in d]
            if V==(4,):assert minor(dp,2)==(3,-2) and sign(minor(dp,2))<0
            else:
                for n in range(2,len(dp)-1):cert.add(minor(dp,n))
            if u+length>=8:continue
            for alpha in range(1,u+1):
                N=alpha+2*u+sum(V)+5
                F=arm_prefix(alpha,[2]*u+list(V),N)
                D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
                W=sum(V);offset=length+2;m=u-1
                # The single numerator unit at W must be REMOVED for the formal previous read.
                tail=D[W+1:];ell=m+tail.index(max(tail));margins=[]
                for n in range(m,ell):
                    rank=offset+n
                    previous=D[rank-1]-(1 if n==m else 0)
                    M=D[rank]**2-previous*D[rank+1]
                    assert M>=0;margins.append(M);integer_margins.add(M);comparisons+=1
                startups[(u,V,alpha)]=dict(first_mode=ell,margins=margins)
    assert keys==set(produced) and len(keys)==175
    assert sorted(cert)==[tuple(x) for x in qa['complete_small_scalar_margins']] and len(cert)==9266
    assert all(sign(x)>=0 for x in cert)
    produced_startups={(z['u'],tuple(z['V']),z['alpha']):z for z in qa['complete_small_startup_contexts']}
    assert set(startups)==set(produced_startups) and len(startups)==29 and comparisons==70
    for k,z in startups.items():
        assert z['first_mode']==produced_startups[k]['first_mode'] and z['margins']==produced_startups[k]['margins']
    assert sorted(integer_margins)==qa['complete_small_startup_integer_margins'] and len(integer_margins)==35
    src=(ROOT/(finite_name+'.lean')).read_text(encoding='utf8')
    lean_rows=[tuple(map(int,x)) for x in re.findall(r'^  \((-?\d+), (-?\d+)\)',src,re.M)]
    assert lean_rows==sorted(cert)
    match=re.search(r'def actualStartupMargins : List ℤ := \[([^]]*)\]',src)
    assert match and list(map(int,match.group(1).split(', ')))==sorted(integer_margins)
    ctrl=qa['actual_earlier_LC_negative_control'];F=arm_prefix(2,[2]*4+[3,3],15)
    triple=[F[n]-F[n-1] for n in (6,7,8)]
    assert triple==ctrl['triple']==[8,12,19] and triple[1]**2-triple[0]*triple[2]==ctrl['margin']==-8
    if '--reconstruct-only' in sys.argv:
        print(json.dumps(dict(status='PASS_INDEPENDENT_COMPLETE_RECONSTRUCTION_ONLY',quotient_contexts=175,field_margins=9266,startup_contexts=29,comparisons=comparisons,integer_margins=35)),flush=True)
        return
    kernels={'DegreeBoundaryCI':kernel('DegreeBoundaryCI',names)}
    kernels[finite_name]=kernel(finite_name,['golden_fine_interval','all_scalar_margins'])
    log=(ROOT/(finite_name+'.log')).read_text(encoding='utf8')
    assert "'"+finite_name+".complete_actual_startup_margins' does not depend on any axioms" in log
    assert log.count('does not depend on any axioms')==1
    kernels[finite_name]['complete_actual_startup_margins']=[]
    files=['degree_boundary_CI_entrance_proof.tex','DegreeBoundaryCI.lean','DegreeBoundaryCI.log',
        finite_name+'.lean',finite_name+'.log','audit_degree_boundary_CI_entrance.py',
        'audit_degree_boundary_CI_entrance.json','emit_degree_boundary_CI_certificate.py',
        'verify_degree_boundary_CI_entrance.py','all_padding_CI_entrance_verification.json',
        'all_padding_CI_entrance_theorem.tex','golden_signed_primitive_cut_closure.tex',
        'divided_CI_later_primitive_proof.tex','infinite_padding_full_deficit_LC.tex',
        'binary_CI_infinite_padding_entrance.tex','lc_positive_primitive_window_closure.tex',
        'homogeneous_reference_complete_C.tex','general_one_jump_complete_C.tex']
    out=dict(status='PASS_UNBOUNDED_DEGREE_BOUNDARY_CI_ENTRANCE_AND_LATE_C',new_scoped_reports=14,kernels=kernels,
        robust='For EVERY u>=16 and EVERY nonnegative LC numerator N with N0=1,N1<=u/2, NO numerator degree bound, B=NQ_u satisfies M_B(s)>=4q^s(Bnext+2qB+q^2Bprev) at EVERY 2<=s<=u-1, INCLUDING the final centre. Full ULC kernel rows, missing N_(s+1), quadratic-geometric last-row budget and row-zero payments are written and scalar-kernel checked.',
        quotient='At EXACT degree boundary u=h>=2, EVERY CI quotient J=((1+z)^uL-psi^u L(-phi))/(1+qz) is positive global LC. Its positive primitive is LC at EVERY centre>=2, EXCEPT the ONE quotient L=[4],u=3 whose centre2 is 3-2phi<0. Uniform u>=16 proof uses registered surplus old quotient, new FOURFOLD arbitrary-degree robust head, enlarged junction range 2r<=u-2, positive u/25 perturbed gap and explicit single-interval endpoints. COMPLETE175 low-u contexts independently reverse-divided,9266 distinct scalar margins.',
        coefficient='For EVERY nonempty CI L degree h, EVERY m>=h-1 and EVERY alpha>=1, formal A=(L*sum(k=0..m)(z+z^2)^k-z^(m+alpha)(1+z)^(m+1)L)^+ is LC at ALL m<=n<=FIRST_A_mode. At NEW boundary m=h-1,c in(0,1), actual preceding C coefficient is SMALLER than its zero-extended geometric inverse, so the first minor improves. Signed-primitive cut and source startup close every padding; exceptional [4] quotient is handled by COMPLETE29 small-w startups/70 coefficient comparisons/35 integer margins. Old m>=h theorem reused without recounting.',
        actual='EVERY ACTUAL sorted V>=3, h=sum(t-1),W=sumV, EVERY binary count u>=h and EVERY padding alpha>=1 satisfies ALL C shifts R>=3 at EVERY N>=W+1. NEW single count u=h has actual LC only required from centre W+2 through FIRSTDmode; centre W+1 MAY FAIL and is NOT asserted. Exact conjugate entrance error c in(0,1) makes first defective ratio STRICTLY below phi. ALL early cumulative reads have reference ratios>phi; ONE ordinary seed at W+1 and finite F/G integration close all later reads. h=2 one-tail base uses established general one-jump C; u>=h+1 uses old theorem.',
        obstruction='Actual earliest LC at u=h is FALSE: V=(3,3),u=4,alpha=2 has D6,D7,D8=(8,12,19), minor -8 at W+1. The new join avoids that centre. Quotient primitive exception [4],u=3 is retained separately; neither refutes actual C.',
        finite_reduction='The shorter binary-count complement now reduces to 0<=u<h, rather than u<h+1, for EACH fixed nonbinary tail. Earlier reference C at N<=W is still OPEN. No general-C least-count or original least-counterexample numerical bound is upgraded.',
        formal_scope='FOURTEEN NEW reports: ELEVEN DegreeBoundaryCI scalar/power/junction/boundary/C-join kernels and THREE DegreeBoundaryCIChunkCertificate reports, including ONE axiom-free integer certificate. Ordinary Lean reduction over25 bounded chunks, no native axiom. Independent capacity-multiset grammar/reverse division rebuilds all175 small quotient contexts; literal actual F/D with its PREVIOUS extra unit correctly removed rebuilds all29 formal startups. Window/convolution/ULC assembly, actual source identities and arbitrary-arm joining are written proofs, not an end-to-end Lean theorem of compositions.',
        remaining='u<h; arbitrary-tail earlier reference C N<=W; general C/A2 and remaining original mixed/deep/incoming branches; ORIGINAL general unamplified coefficient UI OPEN. First unresolved general-C count6 unchanged; NO original numerical bound upgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',independent_small_contexts=175,
        independent_small_startups=29,field_margins=9266,integer_margins=35,QA=qa['counts'],state_sha256=qa['state_sha256'],
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'degree_boundary_CI_entrance_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
