"""Complete canonical h2/h3 owner complement after frozen analytic reductions."""
from pathlib import Path
from collections import Counter
import sys,json,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
def at(p,n):return p[n] if 0<=n<len(p) else 0
def main():
    ct=Counter();sha=hashlib.sha256();states=[];exceptions=[];margins=set()
    for alpha in [1,2]:
        limit=56 if alpha==1 else 36
        for first in range(2,alpha+2):
            words=[[first,t] for t in range(first,limit+1) if first+t-2<=limit]
            words += [[first,L,t] for L in range(first,limit+1) for t in range(L,limit+1)
                if first+L+t-3<=limit]
            for U in words:
                D=sum(t-1 for t in U);A=arm(alpha,U)[:-2];a=len(A)-1;q=A[::-1]
                s=[v-at(q,r-1) for r,v in enumerate(q)];rows=[]
                for r in range(a):
                    C=s[r+1]-s[r]
                    if s[r]<0 or C<=0:continue
                    n=a-r-7;pay=sum(c*at(A,n-j) for j,c in enumerate([1,0,1,2,4,8]));margin=pay-C
                    row=dict(r=r,curvature=C,birth_index=n,payment=pay,margin=margin)
                    rows.append(row);ct['all_positive_curvature_edges']+=1
                    if margin<0:
                        assert r==0
                        exceptions.append(dict(alpha=alpha,U=U,D=D,weight=a,**row));ct['unpaid_exception_edges']+=1
                    else:margins.add(margin);ct['kernel_payment_obligations']+=1
                state=dict(alpha=alpha,U=U,D=D,weight=a,forward=A,reverse=q,ALL_curvature_rows=rows)
                states.append(state);ct['complete_owner_states']+=1
                sha.update(json.dumps(state,separators=(',',':')).encode())
    assert len(states)==1441 and len(exceptions)==6
    values=sorted(margins)
    data=dict(status='COMPLETE_KAPPA_EIGHT_CANONICAL_OWNER_PROOF_INPUTS',counts=dict(ct),states=states,
        exceptions=exceptions,integer_margins=values,state_sha256=sha.hexdigest(),
        scope='ALLcanonicalalpha1/2,h2/3,first<=alpha+1,D<=56/36;AFTEROLDabsolute8h4/initialexchange/gap5/finiteownernecessaryreductions. Negative-r/onepartcaseshandledanalytically;NOTsampledopposites.')
    (ROOT/'kappa_eight_owner_certificate_data.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf8')
    lines=['import Mathlib','set_option maxHeartbeats 0','namespace KappaEightOwnerCertificate',''];chunks=[];exprs=[]
    for i in range(0,len(values),140):
        name='chunk_'+str(i//140);chunks.append(name)
        expr=' && '.join(f'decide ((0 : Int) ≤ {v})' for v in values[i:i+140]);exprs.append('('+expr+')')
        lines += ['private theorem '+name+' : ('+expr+') = true := by decide','']
    lines += ['theorem complete_all_owner_payments : ('+' && '.join(exprs)+') = true := by',
        '  simp only ['+', '.join(chunks+(['Bool.and_self'] if len(chunks)>1 else []))+']',
        'end KappaEightOwnerCertificate','#print axioms KappaEightOwnerCertificate.complete_all_owner_payments']
    (ROOT/'KappaEightOwnerCertificate.lean').write_text('\n'.join(lines)+'\n',encoding='utf8')
    print(json.dumps(dict(counts=dict(ct),exceptions=exceptions,unique_margins=len(values),chunks=len(chunks),sha256=sha.hexdigest())),flush=True)
if __name__=='__main__':main()
