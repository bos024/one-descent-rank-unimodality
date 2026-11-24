"""Independent positive-box and rational-diagonal checks; no finite theorem premise."""
from pathlib import Path
from math import comb
from random import Random
from collections import Counter
import hashlib,json,sys
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,sign
from verify_subdegree_CI_entrance import suffix_boxes
from probe_divided_CI_positive_primitive import divided
from verify_divided_CI_surplus_three_primitive import kernel
ROOT=Path(__file__).resolve().parent
Z=(0,0)
NAMES=['ternary_base_positive','even_kernel_block','odd_kernel_block',
 'ternary_negative_atoms_paid','ternary_first_pair_identity','ternary_third_pair_identity',
 'bottom_source_row','penultimate_read_lower','penultimate_unit_payments','three_factor_norm',
 'old_two_junction_scalar','old_two_junction_gap','three_factor_perturbed_junction',
 'earlier_kernel_scalar','earlier_zero_row','binomial_growth_payment','earlier_read_payment']

def intconv(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
def det(a,n):return sub(mul(a[n],a[n]),mul(a[n-1],a[n+1]))

def main():
    qa=json.loads((ROOT/'audit_three_factor_earlier_cut.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_THREE_FACTOR_EARLIER_CUT_UNDER_AUDIT'
    ct=Counter();sha=hashlib.sha256();N=46
    den=intconv(intconv([1,-1],[1,0,-2,0,1]),[1,-2]);num=[(1,0),(0,-2),(1,1)];G=[]
    for n in range(N+1):
        z=num[n] if n<len(num) else Z
        for k in range(1,min(n,len(den)-1)+1):z=sub(z,mul((den[k],0),G[n-k]))
        G.append(z)
        assert (sign(z)<0)==(n in (1,3))
    for e in range(8):
        Ge=[Z]*(N+e+1)
        for n,z in enumerate(G):
            for k in range(e+1):Ge[n+k]=add(Ge[n+k],mul((comb(e,k),0),z))
        for k in range(3,N+1):
            val=Z
            for l in range(1,k+1):
                top=l*comb(3*k,k-l);assert top%k==0
                val=add(val,mul((top//k,0),Ge[l]))
            j=k-1;u=3*j+e;U=[1,u+3]
            for n in range(2,j+2):
                top=(u+3)*U[-1]+(n+1-u)*U[-2];assert top%n==0;U.append(top//n)
            direct=(U[j+1]+U[j-1],U[j-1]-2*U[j])
            assert direct==val and sign(sub(direct,(3,0)))>0
            ct['independent_signed_diagonal_identities']+=1;sha.update(json.dumps([e,k,val]).encode())
    generated={(d['u'],tuple(d['V']),d['delta']) for d in qa['complete_small_contexts']}
    keys=set();contexts=[]
    for u in range(14,24):
        for a in range(4,u+2):
            for b in range(a,u+2):
                for c in range(b,u+2):
                    delta=a+b+c-3-u
                    if 3<=delta<=a-1 and a+b-2<=u:
                        key=(u,(a,b,c),delta);keys.add(key);contexts.append((u,[a,b,c],delta,True))
    assert keys==generated and len(keys)==670
    rng=Random(202610291121)
    for _ in range(140):
        V=sorted(rng.choices(range(4,53),k=3));delta=rng.randint(3,V[0]-1);u=sum(t-1 for t in V)-delta
        if u>=14:contexts.append((u,V,delta,False))
    for u,V,delta,complete in contexts:
        L=[1]
        for t in reversed(V):L=intconv([1]*t,L)
        E,J=divided(L,u);b=min(u//3,delta)
        g=[]
        for n in range(b,len(J)):
            z=sub(J[n],J[n-1] if n else Z);g.append(z if sign(z)>0 else Z)
        for n in range(1,len(g)-1):assert sign(det(g,n))>=0;ct['independent_full_earlier_primitive_minors']+=1
        for j in range(2,b+1):
            assert sign((E[j+1]+E[j-1],E[j-1]-2*E[j]))>0;ct['independent_actual_source_curvatures']+=1
        alphas=range(1,(2*u+delta)//2+2) if complete else {1,2,delta,u+delta+2}
        for alpha in alphas:
            F=suffix_boxes(alpha,[2]*u+V);W=sum(V);D=[max(0,F[n]-F[n-1]) for n in range(W,len(F))];M=D.index(max(D))
            for n in range(1,M):assert D[n]**2>=D[n-1]*D[n+1];ct['independent_actual_late_D_LC_minors']+=1
            ct['independent_actual_hosts']+=1;ct['independent_complete_small_hosts']+=complete
        ct['independent_CI_profiles']+=1;sha.update(json.dumps([u,V,delta,b,J,g],separators=(',',':')).encode())
    if '--reconstruct-only' in sys.argv:
        print(json.dumps(dict(status='PASS_INDEPENDENT_THREE_FACTOR_EARLIER_CUT_RECONSTRUCTION',counts=dict(ct),state_sha256=sha.hexdigest())),flush=True);return
    kernels={'ThreeFactorEarlierCut':kernel('ThreeFactorEarlierCut',NAMES)}
    deps=['convex_tilt_Lagrange_three_factor_verification.json','double_subdegree_CI_entrance_verification.json',
          'mode_only_uniform_tail_closure_verification.json']
    for path in deps:
        dep=json.loads((ROOT/path).read_text(encoding='utf8'))
        for name,digest in dep['sha256'].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    files=['three_factor_earlier_cut_proof.tex','ThreeFactorEarlierCut.lean','ThreeFactorEarlierCut.log',
           'audit_three_factor_earlier_cut.py','audit_three_factor_earlier_cut.json','verify_three_factor_earlier_cut.py',
           'double_subdegree_support_clarification.tex','golden_signed_primitive_cut_closure.tex']+deps
    out=dict(status='PASS_UNBOUNDED_ALL_THREE_FACTOR_CROSSINGS_AND_CONSTANT_TWO_FACTOR_ENTRANCE',
        new_scoped_reports=len(NAMES),kernels=kernels,state_sha256=qa['state_sha256'],QA=qa['counts'],
        independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),new_finite_entrance_certificates=0,
        source='PROVED ALLj>=2,u>=3j: Q3(u,j)>3. Signed ternary Lagrange kernel has precisely two negative atoms, at1/3. Coefficientwise w^l-t^l<=3l*w^(l+1) pairs them against degrees2/4; every other coefficient positive. Extension to u>3j is by Pascal induction, NOT unjustified positivity after multiplication of a signed kernel. True capacity cuts through min(floor(u/3),delta) are paid.',
        earlier_primitive='PROVED ALL three-factor minimal crossings,u>=14,delta>=3: the ORIGINAL positive J-primitive truncated below min(floor(u/3),delta) is global LC. Natural tail and penultimate unit kernels use norm<5/6 and oldCount2 gap. Earlier prefix uses an exponentially growing BINOMIAL bound, verified by a written unbounded induction from m5; u14 is one generic scalar base, NOT a finite host entrance.',
        three_factor='PROVED EVERY deletion-minimal THREE-factor CI crossing, ALL binary counts/capacities/paddings: actual positive D tail from physical W has LC at every pre-first-tail-mode internal centre. u<=13 old theorem; u>=14 wholly analytic. Full finite source at rank0 and actual previous unit retained. Independent full small profiles/paddings are QA ONLY.',
        constant_two_reduction='Universal actual late-D-LC for ALL h>u now needs ONLY TWO CI FACTORS in a minimal crossing, after old long-factor/degree-u+1/degree-u+2 seeds and arbitrary insertion. Remainingu>=14, r2, 3<=d1<=d2<=u, u+3<=h=d1+d2<=2u; delta=h-u<=d1. This two-factor entrance remains OPEN and no finite numerical cutoff resolves it.',
        formal_scope='SEVENTEEN new scoped kernel reports: unbounded signed-diagonal base positivity, parity blocks, negative-atom payments, explicit polynomial identities, source bottom row, penultimate bounds, norm, junction and earlier head scalars. Power series, binomial coefficient induction, Toeplitz and actual composition assembly are written, not an end-to-end Lean theorem. No new finite theorem certificate.',
        remaining='Remaining late-D-LC entrance now ONLY TWO factors. Earlier C and C entrance, A2 and original general unamplified coefficient UI remain OPEN. Actual late-C threshold u>=h-2 unchanged; first original unresolved full-C count6 unchanged.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',actual_late_C_threshold='u>=h-2 UNCHANGED',
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'three_factor_earlier_cut_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
