"""Exact QA for the symbolic infinite-three / repeated-four C theorem."""
from pathlib import Path
from collections import Counter
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_renewal_root_primitive_cut import ReciprocalRing
def renewal(t,N):
    h=[1]
    for n in range(1,N+1):h.append(sum(h[max(0,n-t):n]))
    return h
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256()
    for s in range(0,111):
        W=4*s;Nmax=W+90;h=renewal(3,Nmax);h4=renewal(4,Nmax);F=h[:]
        for _ in range(s):F=[1]+[sum(F[max(0,n-4):n]) for n in range(1,Nmax+1)]
        G=[];v=0
        for x in F:v+=x;G.append(v)
        d=[F[n]-(F[n-1] if n else 0) for n in range(len(F))]
        if s:
            A=s+4;assert F[:A]==h4[:A] and h4[A]-F[A]==1
            c=(2**s-1)*(2**s-2)//6;a=2**s;g3=[];v=0
            for x in h:v+=x;g3.append(v)
            for n in range(W-2,Nmax+1):assert F[n]==a*h[n-s];ct['EXACTwhole_homogeneous_tail_reads']+=1
            for n in range(W-3,Nmax+1):assert G[n]==a*g3[n-s]-c;ct['EXACTconstant_CDF_tail_reads']+=1
            assert G[W-4]==a*(g3[3*s-4] if s>=2 else 0)-c+1
            ct['RETAINEDone_unit_CDF_boundary_reads']+=1
            for n in range(A,W-1):
                assert F[n]**2>=F[n-1]*F[n+1];ct['ordinary_entire_physical_head_minors']+=1
            if s>=3:
                aa=[1,s-2,(s-1)*(s-2)//2,s*(s-1)*(s-2)//6+2]
                aj=lambda n:aa[W-3-n] if 0<=W-3-n<4 else 0
                for n in range(W-5,W-1):
                    m=n-s
                    calc=a*a*(h[m]**2-h[m-1]*h[m+1])+a*(aj(n-1)*h[m+1]+aj(n+1)*h[m-1]-2*aj(n)*h[m])+aj(n)**2-aj(n-1)*aj(n+1)
                    assert calc==F[n]**2-F[n-1]*F[n+1];ct['EXACTfour_corner_signed_polynomial_identities']+=1
            if s>=22:
                for n in range(3*s-5,Nmax-1):
                    assert a*abs(h[n]**2-h[n-1]*h[n+1])<=h[n-1]
                    ct['scaled_ternary_ALLtail_unit_minor_QA']+=1
        for n in range(1,Nmax):
            assert G[n]**2>=G[n-1]*G[n+1];ct['GLOBALordinary_CDF_LC_minors']+=1
        for N in range(4,Nmax+1):
            for k in range(1,N-2):
                assert G[k]*d[N-1]>=G[k-1]*d[N],(s,N,k)
                ct['FULLC_ALLcurrent_ALLshift_QA_reads']+=1
        sha.update(str((s,F[-3:],G[-3:])).encode())
    f=ReciprocalRing(3);Nmax=450;h=renewal(3,Nmax)
    a=f.sub(f.l,f.one);b=f.q;e=[f.sub(f.sc(f.one,h[n]),f.sc(f.l,h[n-1] if n else 0)) for n in range(Nmax+1)]
    bn=f.one
    for n in range(1,Nmax+1):
        bn=f.mul(bn,b)
        norm=f.add(f.add(f.mul(e[n],e[n]),f.mul(a,f.mul(e[n],e[n-1]))),f.mul(b,f.mul(e[n-1],e[n-1])))
        assert norm==bn;ct['EXACTwhole_ternary_residual_norm_reads']+=1
    out=dict(status='EXACT_QA_PASS_INFINITE_THREE_FOUR_REFERENCE_COMPLETE_C_AND_GLOBAL_CDF_LC',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='ReferenceALLs theoremusesWHOLEordinaryheadheredity,COMPLETE651minorfixedentrance,ALLfourcorners,WHOLEscaleddecayandCDF/CjoinsincludingEXTRAUNITatN=W. QAisnotanunboundedpremise. Actualfinite3countandgeneraloriginal/C/A2remainOPEN.')
    (ROOT/'audit_infinite_three_four_reference_C.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
