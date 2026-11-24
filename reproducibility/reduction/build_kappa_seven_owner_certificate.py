"""Complete finite owner proof complement after frozen necessary reductions."""
from pathlib import Path
import sys,json,hashlib
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm

def at(a,n):return a[n] if 0<=n<len(a) else 0
def main():
    ct=Counter();sha=hashlib.sha256();states=[];margins=set();exceptions=[]
    words=[[2,t] for t in range(2,37)]
    words += [[2,L,t] for L in range(2,37) for t in range(L,37) if L+t<=37]
    for U in words:
        D=sum(t-1 for t in U);assert D<=36
        A=arm(1,U)[:-2];a=len(A)-1;q=A[::-1]
        ss=[v-at(q,r-1) for r,v in enumerate(q)];rows=[]
        for r in range(len(q)-1):
            C=ss[r+1]-ss[r]
            if ss[r]<0 or C<=0:continue
            n=a-r+1-7;pay=at(A,n)+at(A,n-2);margin=pay-C
            row=dict(r=r,curvature=C,birth_index=n,payment=pay,margin=margin)
            rows.append(row);ct['all_positive_curvature_edges']+=1
            if margin<0:
                assert U in [[2,2],[2,2,2]] and r==0
                exceptions.append(dict(U=U,a=a,D=D,**row));ct['unpaid_exception_edges']+=1
            else:margins.add(margin);ct['kernel_payment_obligations']+=1
        state=dict(U=U,D=D,weight=a,forward=A,reverse=q,ALL_curvature_rows=rows)
        states.append(state);ct['complete_owner_states']+=1
        sha.update(json.dumps(state,separators=(',',':')).encode())
    assert len(exceptions)==2
    values=sorted(margins)
    data=dict(status='COMPLETE_KAPPA_SEVEN_CANONICAL_OWNER_PROOF_INPUTS',counts=dict(ct),states=states,exceptions=exceptions,
        integer_margins=values,state_sha256=sha.hexdigest(),
        scope='COMPLETEallalpha1/first2/h2or3/D<=36owners,AFTEROLDgap5/gap6h4/initialexchange/finiteownernecessaryreductions. Not sampled opposite profiles.')
    (ROOT/'kappa_seven_owner_certificate_data.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf8')
    lines=['import Mathlib','set_option maxHeartbeats 0','namespace KappaSevenOwnerCertificate',''];chunks=[];exprs=[]
    for i in range(0,len(values),140):
        name='chunk_'+str(i//140);chunks.append(name)
        expr=' && '.join(f'decide ((0 : Int) ≤ {v})' for v in values[i:i+140]);exprs.append('('+expr+')')
        lines += ['private theorem '+name+' : ('+expr+') = true := by decide','']
    lines += ['theorem complete_all_owner_payments : ('+' && '.join(exprs)+') = true := by',
        '  simp only ['+', '.join(chunks+(['Bool.and_self'] if len(chunks)>1 else []))+']',
        'end KappaSevenOwnerCertificate','#print axioms KappaSevenOwnerCertificate.complete_all_owner_payments']
    (ROOT/'KappaSevenOwnerCertificate.lean').write_text('\n'.join(lines)+'\n',encoding='utf8')
    print(json.dumps(dict(counts=dict(ct),exceptions=exceptions,unique_margins=len(values),chunks=len(chunks),sha256=sha.hexdigest())),flush=True)
if __name__=='__main__':main()
