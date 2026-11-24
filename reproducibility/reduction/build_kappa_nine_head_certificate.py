"""Complete rational-rank and finite-owner proof inputs for K=9 proper head payment."""
from pathlib import Path
from fractions import Fraction
from math import comb
from collections import Counter
import sys,json,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
def at(p,n):return p[n] if 0<=n<len(p) else 0
def parts(n,h,lo=1):
    if h==0:
        if n==0:yield []
        return
    for v in range(lo,n//h+1):
        for rest in parts(n-v,h-1,v):yield [v]+rest
def rank_payment(d,r,e):
    L=d-e-3
    def t(m):return Fraction(comb(r,m),comb(r+e+m+2,m)) if 0<=m<=r else Fraction(0)
    return t(L)+sum(2**(i-2)*t(L+i) for i in range(2,7))-Fraction(e+1,r+1)
def main():
    ct=Counter();states={};ranks=[];rows=[];exceptions=[];integers=set();sha=hashlib.sha256()
    for alpha in [1,2,3]:
        d=9-alpha;Dmax=min(2*d*(d-3),12*d-25)
        for e in range(d-2):
            for r in range((Dmax-e-2)//2+1):
                D=2*r+2+e;p=rank_payment(d,r,e);paid=p>=0
                rank=dict(alpha=alpha,d=d,e=e,r=r,D=D,numerator=p.numerator,denominator=p.denominator,paid=paid)
                ranks.append(rank);ct['complete_rank_states']+=1
                if paid:
                    ct['rational_rank_states_paid']+=1;integers.update([p.numerator,p.denominator-1]);continue
                ct['unpaid_rank_states']+=1
                for h in range(2,min(D,3 if alpha==3 else 5)+1):
                    for ds in parts(D,h):
                        if ds[0]>alpha:continue
                        U=[v+1 for v in ds];key=(alpha,tuple(U))
                        if key not in states:
                            A=arm(alpha,U)[:-2];q=A[::-1]
                            states[key]=dict(alpha=alpha,U=U,D=D,weight=len(A)-1,forward=A,reverse=q)
                        state=states[key];A=state['forward'];q=state['reverse'];a=len(A)-1
                        sr=at(q,r)-at(q,r-1);C=at(q,r+1)-2*at(q,r)+at(q,r-1);j=a-r;n=j-8
                        pay=at(A,n)+sum(2**(i-2)*at(A,n-i) for i in range(2,7))
                        row=dict(alpha=alpha,U=U,D=D,r=r,primitive=sr,curvature=C,
                            shared_rank=j,birth_index=n,payment=pay)
                        ct['complete_owner_rank_inputs']+=1
                        if sr<0:kind='negative_primitive';margin=-sr-1;ct['noncritical_negative_primitive']+=1
                        elif C<=0:kind='nonpositive_curvature';margin=-C;ct['noncritical_nonpositive_curvature']+=1
                        elif C<=pay:
                            kind='source_paid';margin=pay-C;ct['positive_curvature_owner_rank_inputs']+=1;ct['direct_source_owner_payments']+=1
                        else:
                            kind='strict_head';margin=10-j;assert margin>=0
                            ct['positive_curvature_owner_rank_inputs']+=1;ct['unpaid_positive_curvature_edges']+=1
                            exceptions.append(dict(alpha=alpha,U=U,weight=a,D=D,r=r,curvature=C,shared_rank=j,payment=pay))
                        row.update(kind=kind,margin=margin);integers.add(margin);rows.append(row)
    states=list(states.values());ct['distinct_canonical_owners']=len(states)
    assert len(ranks)==406 and len(rows)==4377 and len(states)==2143 and len(exceptions)==19
    for x in ranks+states+rows:sha.update(json.dumps(x,separators=(',',':')).encode())
    values=sorted(integers)
    data=dict(status='COMPLETE_KAPPA_NINE_SOURCE_OR_STRICT_HEAD_PROOF_INPUTS',counts=dict(ct),
        ranks=ranks,states=states,ALL_owner_rank_rows=rows,exceptions=exceptions,integer_margins=values,
        state_sha256=sha.hexdigest(),scope='Complete406rankstatesafterOLDgap/finiteownerbounds;291rationalpaid,115complementD<=25;ALL2143owners/4377inputs. ALLpositivecurvaturesource-unpaidcandidateshavej<=10. NOsampledoppositepremise.')
    (ROOT/'kappa_nine_head_certificate_data.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf8')
    lines=['import Mathlib','set_option maxHeartbeats 0','namespace KappaNineHeadCertificate',''];chunks=[];exprs=[]
    for i in range(0,len(values),120):
        name='chunk_'+str(i//120);chunks.append(name)
        expr=' && '.join(f'decide ((0 : Int) ≤ {v})' for v in values[i:i+120]);exprs.append('('+expr+')')
        lines += ['private theorem '+name+' : ('+expr+') = true := by decide','']
    lines += ['theorem complete_all_rank_source_or_head_obligations : ('+' && '.join(exprs)+') = true := by',
        '  simp only ['+', '.join(chunks+(['Bool.and_self'] if len(chunks)>1 else []))+']',
        'end KappaNineHeadCertificate','#print axioms KappaNineHeadCertificate.complete_all_rank_source_or_head_obligations']
    (ROOT/'KappaNineHeadCertificate.lean').write_text('\n'.join(lines)+'\n',encoding='utf8')
    print(json.dumps(dict(counts=dict(ct),max_D=max(x['D'] for x in ranks if not x['paid']),
        max_unpaid_j=max(x['shared_rank'] for x in exceptions),unique_margins=len(values),chunks=len(chunks),sha256=sha.hexdigest())),flush=True)
if __name__=='__main__':main()
