"""Independent exhaustive reconstruction; no imports of entrance generator.

Actual polynomials are reconstructed as a sum of suffix interval products
plus the full product times the initial indicator. This is different from
the per-arm prefix recurrence used by the entrance generator.
"""
from pathlib import Path
from collections import Counter
from itertools import accumulate
from math import prod
import hashlib,json,re,time
from audit_joint_structure import fastconv

ROOT=Path(__file__).resolve().parent


def suffix_layers(U):
    Q=[1];Z=[0]
    for t in reversed(U):
        if len(Z)<len(Q):Z += [0]*(len(Q)-len(Z))
        for i,a in enumerate(Q):Z[i]+=a
        Q=fastconv(Q,[0]+[1]*t)
    return Z,Q


def read(seq,n):return seq[n] if 0<=n<len(seq) else 0


def actual_from_layers(Z,Q,alpha,M):
    I=list(accumulate(Q))
    def cum(n):return 0 if n<0 else I[min(n,len(I)-1)]
    return [read(Z,n)+cum(n)-cum(n-alpha-1) for n in range(M+2)]


def all_C(F,D,M,counts,literal):
    G=list(accumulate(F));p=1
    for n in range(3,M+1):
        k=n-3
        if k>=1 and G[k]*G[p-1]<G[p]*G[k-1]:p=k
        if D[n]>D[n-1]:
            counts['ALL_C_shifts_covered_at_increasing_current_ranks']+=max(0,n-3)
            if k>=1:
                assert G[p]*D[n-1]>=G[p-1]*D[n]
                counts['exact_prefix_minimum_ALL_shift_C_payments']+=1
            if literal:
                for j in range(1,n-2):
                    assert G[j]*D[n-1]>=G[j-1]*D[n]
                    counts['independent_literal_ALL_shift_C_checks']+=1


def main():
    start=time.monotonic();datafile='multitail_binary_prefix_finite_entrance_weight32.json'
    data=json.loads((ROOT/datafile).read_text());assert data['status']=='PASS_EXHAUSTIVE_FIXED_MULTITAIL_FINITE_ENTRANCES'
    bound=data['nonbinary_tail_weight_bound'];assert bound==32
    # Independent bottom-up generation of every sorted capacity multiset.
    byweight=[set() for _ in range(bound+1)];byweight[0].add(())
    for t in range(3,bound+1):
        for w in range(t,bound+1):
            for V in byweight[w-t]:byweight[w].add(V+(t,))
    expected=set().union(*byweight[1:]);certs=data['certificates']
    assert len(certs)==len(expected)==len({tuple(x['V']) for x in certs})
    assert {tuple(x['V']) for x in certs}==expected
    counts=Counter();digest=hashlib.sha256()
    for wi,cert in enumerate(certs,1):
        V=tuple(cert['V']);W=sum(V);r=len(V);h=W-r;H=h+4;M=2*H+W
        assert (cert['W'],cert['H'],cert['alpha_entrance_bound'],cert['rank_entrance_bound'])==(W,H,H+h+1,M+1)
        fib=[0,1]
        for _ in range(M+6):fib.append(fib[-1]+fib[-2])
        ZV,QV=suffix_layers(V)
        refprod=fastconv(QV,[fib[n+1] for n in range(M+2)])
        ref=[read(ZV,n)+read(refprod,n) for n in range(M+2)]
        rd=[0,0]+[ref[n]-ref[n-1] for n in range(2,len(ref))]
        all_C(ref,rd,W+5,counts,wi%97==1)
        counts['complete_early_reference_profiles']+=1
        A=prod(fib[t-1]+fib[t+1]-1-(-1)**t for t in V)
        assert A==cert['Cassini_amplitude']==abs(rd[W+3]**2-rd[W+2]*rd[W+4])
        a,b=1,0
        for t in V:
            a,b=(fib[t+2]-1)*a+(fib[t+1]-1)*b,(fib[t+1]-1)*a+fib[t]*b
        assert (a,b)==(rd[W+2],rd[W+1])
        assert a*a-b*(a+b)==A
        assert rd[W+2]>=A and rd[W+4]>=2*A+1
        counts['whole_word_Cassini_amplitude_and_seed_budgets']+=1
        local=Counter()
        for u in range(H+1):
            m=2*u+W;b=u+h+1
            Z,Q=suffix_layers([2]*u+list(V))
            for alpha in range(1,b+1):
                F=actual_from_layers(Z,Q,alpha,m)
                D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
                assert D[m+1]==0
                ell=D.index(max(D))
                if u==H:
                    N0=u+r+2
                    assert F[:N0]==ref[:N0]
                    assert ref[N0]-F[N0]==(2 if alpha==1 else 1)
                    for n in range(N0-1,ell):
                        assert D[n]**2>=D[n-1]*D[n+1]
                        counts['exhaustive_entrance_rising_tail_LC_minors']+=1
                        local['LC_minors']+=1
                    counts['exhaustive_entrance_alpha_representatives']+=1
                    local['entrance_profiles']+=1
                else:
                    counts['exhaustive_shorter_binary_count_alpha_representatives']+=1
                    local['shorter_profiles']+=1
                all_C(F,D,m,counts,wi%97==1 and alpha in (1,b))
                if alpha==b:
                    assert actual_from_layers(Z,Q,b+m+17,m)==F
                    counts['independent_padding_clamp_prefix_checks']+=1
                digest.update(json.dumps([V,u,alpha,F,D,ell],separators=(',',':')).encode())
            
        assert dict(local)==cert['counts']
        counts['ALL_sorted_nonbinary_tail_words']+=1
        if r>=6:counts['tail_words_with_at_least_six_nonbinary_capacities']+=1
        if wi%300==0:print(json.dumps(dict(independently_rebuilt_words=wi,seconds=round(time.monotonic()-start,2))),flush=True)
    assert dict(counts)==data['counts'],(dict(counts),data['counts'])
    assert digest.hexdigest()==data['complete_state_sha256']
    source=(ROOT/'MultitailCassiniBudget.lean').read_text();log=(ROOT/'MultitailCassiniBudget.log').read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
    assert 'error:' not in log and 'warning:' not in log
    names=['all_capacity_Cassini_factor_bound','full_Fibonacci_window_identity',
        'all_word_exact_Cassini_amplitude','all_word_reference_Cassini_budget',
        'nonempty_word_two_step_strict_budget','first_defect_strict_LC_payment']
    kernels={}
    for name in names:
        match=re.search(r"'MultitailCassiniBudget\."+name+r"' depends on axioms: \[([^]]*)\]",log)
        assert match,name
        axioms={x.strip() for x in match.group(1).split(',') if x.strip()}
        assert axioms<={'propext','Classical.choice','Quot.sound'},(name,axioms)
        kernels[name]=sorted(axioms)
    dependencies=['arbitrary_Fibonacci_tail_late_C_verification.json','general_one_jump_analytic_C_verification.json']
    files=['multitail_binary_prefix_finite_principle.tex','MultitailCassiniBudget.lean','MultitailCassiniBudget.log',
        'certify_multitail_binary_prefix_finite_principle.py',datafile,
        'verify_multitail_binary_prefix_finite_principle.py','audit_minimum_staircase_scaled_dyadic.py',
        'audit_arbitrary_Fibonacci_tail_late_C.py','audit_joint_structure.py']
    for depfile in dependencies:
        dep=json.loads((ROOT/depfile).read_text())
        assert dep['status'].startswith('PASS_')
        for f,sha in dep['sha256'].items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==sha,f
        files.append(depfile);files+=list(dep['sha256'])
    out=dict(status='PASS_UNBOUNDED_FIXED_MULTITAIL_FINITE_PRINCIPLE_AND_NONBINARY_WEIGHT32_COMPLETE_C',
        new_scoped_reports=6,kernels=kernels,
        finite_principle='ANY fixed sorted V>=3, r=count,W=sum,h=W-r,H=h+4: ordinary positiveD LC only throughFIRSTDmode at SINGLEu=H andfinitealpha<=H+h+1 implies ALLlateC atEVERYN>=W+6 forallu>=H/ALLalpha. AddreferenceC N<=W+5 forcompleteC allu>=H; finiteactualshorter u<H,alpha<=u+h+1 closesALLu>=0. Exactordinaryreads<=2u+W+1, NEVER assumes LCafteroldFIRSTmode.',
        analytic_budget='ALLword Cassini amplitudeA=product C_t, Ct=Fib(t-1)+Fib(t+1)-1-(-1)^t. Exacthomogeneouswindowidentity and Ct<=Fib(t+2)-1 imply r_(W+2)>=A, r_(W+4)>=2A+1. FirstactualdefectpaysSTRICTLCminor>=A+1, ALLwordcounts/capsUNBOUNDED. Generalreference lateC atN0>=W+6 +TWOearlyDseeds +F/Gfinite-readintegration closesALLshiftsafterentrance.',
        proved_actual_family='COMPLETE C for EVERY sorted actual 1^alpha 2^u V, alpha>=1,u>=0,nonemptyVentries>=3,sumV<=32. ALLbinarycounts/padding/currentranks/shiftsUNBOUNDED. EmptyV alreadyclosedbinarytheorem. 2744fixedtails, including tails with>=6nonbinarycapacities. Exhaustivefiniteentrances independentlyreconstructed by suffixCI-layerpolynomials, completeSTATEbytes/counts/hashMATCH. No endtoend Lean finiteactualcomposition claim.',
        formal_scope='SIXnewstandardaxiomkernelreports: ALLcapacityfactorbound, exactALLlengthFibonacciwindowidentity, FULLwordEXACTCassiniamplitudeidentity, FULLunboundedwordCassini-statebudgetinduction, nonemptywordstrict2stepbudget, firstdefectstrictLCpayment. ExistingFULLrising-taildiagonalinduction and TWOseed/finite-readintegration kernelsREUSED withoutrecounting. Actual word/polynomial/mode/padding/reference/completeC assemblyWRITTEN; independentfinitewordreconstruction is exactPython, NOT ordinaryLeanfinitecertificate.',
        remaining='ArbitraryV entranceLC remainsOPEN; finitewordweight32family is not arbitrarytailword. GeneralactualC/A2 andORIGINALgeneralunamplifiedUI OPEN. Nooriginalnumericalleastcounterexampleboundupgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',QA=dict(counts),
        complete_state_sha256=digest.hexdigest(),independent_rebuild_seconds=time.monotonic()-start,
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in sorted(set(files))})
    (ROOT/'multitail_binary_prefix_finite_principle_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
