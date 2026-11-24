"""Independent complete finite entrance and analytic-identity audit, retaining original OPEN."""
from pathlib import Path
from math import comb
from random import Random
from collections import Counter
import hashlib,json,sys,re
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,sign
from verify_subdegree_CI_entrance import suffix_boxes
from probe_divided_CI_positive_primitive import divided
ROOT=Path(__file__).resolve().parent
Z=(0,0)
NAMES=['transported_minor_term','prefix_reference_loss_payment','prefix_reference_C_bound',
 'first_two_window_identity','first_two_window_all_padding','quaternary_kernel_positive',
 'quaternary_odd_block','quaternary_negative_atom_paid','quaternary_pair_polynomial',
 'quaternary_bottom_source','two_factor_atom_norm','regular_geometry',
 'old_one_junction_scalar','old_one_junction_gap','regular_perturbed_junction',
 'left_half_ULC_scalar','left_half_zero_row','left_atom_constants','left_binomial_growth',
 'left_budget_growth','left_binomial_base','right_exponential_bases','right_exponential_step',
 'right_half_budget','right_half_zero_row']

def kernel(module,names):
    src=(ROOT/(module+'.lean')).read_text(encoding='utf8');log=(ROOT/(module+'.log')).read_text(encoding='utf8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(s in log for s in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==len(names)
    out={}
    for name in names:
        hit=re.search("'"+module+r"\."+name+r"' depends on axioms: \[([^]]*)\]",log)
        if hit:
            ax={x.strip() for x in hit.group(1).split(',') if x.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
        else:
            assert "'"+module+'.'+name+"' does not depend on any axioms" in log;ax=set()
        out[name]=sorted(ax)
    return out

def intconv(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
def det(A,n):return A[n]**2-A[n-1]*A[n+1]
def fielddet(A,n):return sub(mul(A[n],A[n]),mul(A[n-1],A[n+1]))

def main():
    qa=json.loads((ROOT/'audit_two_factor_complete_entrance.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_COMPLETE_TWO_FACTOR_LATE_D_LC_ENTRANCE_UNDER_AUDIT'
    ct=Counter();sha=hashlib.sha256();N=45
    den=intconv(intconv([1,0,-2,0,1],[1,1]),[1,-3]);num=[(1,0),(0,-2),(1,1)];G=[]
    for n in range(N+1):
        z=num[n] if n<len(num) else Z
        for k in range(1,min(n,len(den)-1)+1):z=sub(z,mul((den[k],0),G[n-k]))
        G.append(z);assert (sign(z)<0)==(n==1)
    for e in range(9):
        Ge=[Z]*(N+e+1)
        for n,z in enumerate(G):
            for k in range(e+1):Ge[n+k]=add(Ge[n+k],mul((comb(e,k),0),z))
        for k in range(3,N+1):
            val=Z
            for l in range(1,k+1):
                top=l*comb(4*k,k-l);assert top%k==0
                val=add(val,mul((top//k,0),Ge[l]))
            j=k-1;u=4*j+e;U=[1,u+2]
            for n in range(2,j+2):
                top=(u+2)*U[-1]+(n-u)*U[-2];assert top%n==0;U.append(top//n)
            direct=(U[j+1]+U[j-1],U[j-1]-2*U[j])
            assert direct==val and sign(sub(direct,(2,0)))>0
            ct['independent_quaternary_diagonal_identities']+=1;sha.update(json.dumps([e,k,val]).encode())
    produced={(d['u'],tuple(d['V']),d['delta']) for d in qa['finite_entrance_profiles']};keys=set();margins=set()
    for u in range(14,24):
        for delta in range(3,u+1):
            h=u+delta
            for d1 in range(delta,h//2+1):
                d2=h-d1
                if d2+1>u-3:continue
                V=[d1+1,d2+1];key=(u,tuple(V),delta);assert key not in keys;keys.add(key)
                for alpha in range(1,(u+h)//2+2):
                    F=suffix_boxes(alpha,[2]*u+V);W=sum(V);D=[max(0,F[n]-F[n-1]) for n in range(W,len(F))];M=D.index(max(D))
                    for n in range(1,M):
                        z=det(D,n);assert z>=0;margins.add(z);ct['independent_finite_entrance_integer_comparisons']+=1
                    ct['independent_finite_entrance_hosts']+=1
                    sha.update(json.dumps([u,V,alpha,M,D],separators=(',',':')).encode())
    assert keys==produced and len(keys)==245
    assert sorted(margins)==qa['integer_margins'] and len(margins)==43336
    assert ct['independent_finite_entrance_hosts']==5860 and ct['independent_finite_entrance_integer_comparisons']==76201
    for u in list(range(14,43))+[55,79,120]:
        for c in (-1,0,1,2):
            B=u-c;K=c+3
            for alpha in {1,2,3,K,u+2}:
                F=suffix_boxes(alpha,[2]*u+[B]);f=[F[n]-F[n-1] for n in range(B,len(F))];p=[max(0,z) for z in f];M=p.index(max(p))
                if M>K:
                    for i in range(1,K+1):assert f[i]*f[K]>=f[i-1]*f[K+1];ct['independent_long_boundary_prefix_comparisons']+=1
                for A in {K,max(4,K),K+1,B}:
                    if A>B:continue
                    H=suffix_boxes(alpha,[2]*u+sorted([A,B]));W=A+B;D=[max(0,H[n]-H[n-1]) for n in range(W,len(H))];mode=D.index(max(D))
                    for n in range(len(D)):
                        assert D[n]==max(0,sum(f[n:n+A]));ct['independent_actual_forward_window_identity_reads']+=1
                    for n in range(1,mode):assert det(D,n)>=0;ct['independent_long_boundary_late_D_LC_minors']+=1
                    ct['independent_long_boundary_hosts']+=1
    rng=Random(202610291161)
    for _ in range(200):
        V=sorted(rng.choices(range(4,58),k=2));delta=rng.randint(3,V[0]-1);u=sum(t-1 for t in V)-delta
        if u<24 or max(V)>u-3:continue
        L=intconv([1]*V[0],[1]*V[1]);E,J=divided(L,u);b=min(u//4,delta);g=[]
        for n in range(b,len(J)):
            z=sub(J[n],J[n-1] if n else Z);g.append(z if sign(z)>0 else Z)
        for n in range(1,len(g)-1):assert sign(fielddet(g,n))>=0;ct['independent_regular_earlier_primitive_minors']+=1
        for j in range(2,b+1):
            assert sign((E[j+1]+E[j-1],E[j-1]-2*E[j]))>0;ct['independent_actual_quaternary_source_curvatures']+=1
        for alpha in {1,2,delta,u+delta+2}:
            F=suffix_boxes(alpha,[2]*u+V);W=sum(V);D=[max(0,F[n]-F[n-1]) for n in range(W,len(F))];M=D.index(max(D))
            for n in range(1,M):assert det(D,n)>=0;ct['independent_regular_late_D_LC_minors']+=1
            ct['independent_regular_hosts']+=1
        ct['independent_regular_CI_profiles']+=1
    if '--reconstruct-only' in sys.argv:
        print(json.dumps(dict(status='PASS_INDEPENDENT_COMPLETE_TWO_FACTOR_ENTRANCE_RECONSTRUCTION',counts=dict(ct),margins=len(margins),state_sha256=sha.hexdigest())),flush=True);return
    kernels={'TwoFactorCompleteEntrance':kernel('TwoFactorCompleteEntrance',NAMES),
             'TwoFactorEntranceCertificate':kernel('TwoFactorEntranceCertificate',['all_integer_margins'])}
    assert kernels['TwoFactorEntranceCertificate']['all_integer_margins']==['propext']
    src=(ROOT/'TwoFactorEntranceCertificate.lean').read_text(encoding='utf8');cert=[]
    for match in re.finditer(r'def part\d+ : List ℤ := \[([^]]*)\]',src):
        cert.extend(int(x.strip()) for x in match.group(1).split(',') if x.strip())
    assert cert==qa['integer_margins']
    deps=['three_factor_earlier_cut_verification.json','convex_tilt_Lagrange_three_factor_verification.json',
          'double_subdegree_CI_entrance_verification.json','mode_only_uniform_tail_closure_verification.json',
          'general_one_jump_analytic_C_verification.json']
    for path in deps:
        dep=json.loads((ROOT/path).read_text(encoding='utf8'))
        for name,digest in dep['sha256'].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    files=['two_factor_complete_entrance_proof.tex','TwoFactorCompleteEntrance.lean','TwoFactorCompleteEntrance.log',
           'TwoFactorEntranceCertificate.lean','TwoFactorEntranceCertificate.log',
           'audit_two_factor_complete_entrance.py','audit_two_factor_complete_entrance.json',
           'emit_two_factor_entrance_certificate.py','verify_two_factor_complete_entrance.py',
           'double_subdegree_support_clarification.tex','golden_signed_primitive_cut_closure.tex']+deps
    out=dict(status='PASS_UNIVERSAL_ALL_PADDING_ACTUAL_LATE_D_LC_ABOVE_CI_DEGREE_CROSSING',new_scoped_reports=26,
        kernels=kernels,state_sha256=qa['state_sha256'],QA=qa['counts'],independent_counts=dict(ct),
        independent_state_sha256=sha.hexdigest(),finite_profiles=245,finite_hosts=5860,finite_integer_comparisons=76201,distinct_kernel_margins=43336,kernel_chunks=170,
        window_transport='PROVED FOR ANY nonnegative unimodal interval-supported input STRICTLY rising to FIRSTmode: if LC from K through mode AND all earlier ratios dominate first tail ratio, pre-mode LC of forward uniform lengthK implies every lengthA>=K. Signed actual tails use exact positive growing reads. Prefix-ratio premise is ESSENTIAL; arbitrary UI length monotonicity is FALSE.',
        long_boundaries='PROVED ALLu>=14,ALLpadding, maxcap B in {u-2,u-1,u,u+1}, EVERYother minimal crossing capacityA. Old one-jump pre-mode LC from physicalu+3 plus exact prefix loss/Cassini bounds pay all earlier ratios; K=u-B+3<=5. Degreeu+1 seeds pay K3/4/5; exact all-padding first two-window minor pays K2. Actual signed insertion identity, previous unit and finite source retained.',
        regular='PROVED ALLu>=24, maxcap<=u-3, ALLpadding: norm<6/5 below5/4 interior, oldCount1 gap, earlier primitive cutoff min(floor(u/4),delta). Left binomial induction from m6 and RIGHT half binomial/exponential induction from k7..10 pay ENTIRE head. Quaternary signed Lagrange diagonal Q2>2 for ALLu>=4j,j>=2 pays source. Finite theorem premise ONLY245 complete regular profilesu14..23 with ALL5860padding hosts and ALL43336 kernel margins.',
        universal='PROVED EVERY sorted actual word1^alpha2^uV with alpha>=1,V>=3 nonempty,h=sum(t-1)>u: positive actual D tail from physicalW=sumV is LC at EVERY internal centre strictly before its FIRSTtailmode. Equivalent ALL pre-GLOBAL-FIRST-D-mode centres N>=W+1. u0 direct; u1..13 old; EVERY minimal crossing at u>=14 now closed (single/degree-u+1/u+2 old, >=3-factor registered, TWO-factor here); arbitrary insertion propagates to ALL CI multisets. No count/capacity/padding/degree bound.',
        formal_scope='TWENTY-SIX new scoped reports:25 unbounded algebraic/window/prefix/half-band/source kernels plus ONE COMPLETE integer entrance certificate in170chunks, onlypropext. Formal Lagrange is primary literature input; binomial induction, formal-series, actual-word identities, mode/window and hereditary assembly WRITTEN. Not an end-to-end Lean arbitrary-composition proof.',
        remaining='Universal late-D-LC h>u is NOW CLOSED. This alone does NOT prove earlier ordinary/cumulative C entrances, general C, A2 or original unamplified coefficient UI. Actual late-C threshold u>=h-2 and first original unresolved full-C nonone count6 unchanged. h<=u derivative-LC extension is FALSE by registered actual triple8/12/19.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',actual_late_C_threshold='u>=h-2 UNCHANGED',
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'two_factor_complete_entrance_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
