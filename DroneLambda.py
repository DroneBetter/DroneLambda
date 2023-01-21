from functools import reduce
from itertools import chain,pairwise,starmap
from copy import deepcopy
from math import gcd,log
from fractions import Fraction
from numbers import Number
dbg=(lambda x,*s: (x,print(*s,x))[0]) #debug
revange=(lambda a,b=None,c=1: range(b-c,a-c,-c) if b else range(a-c,-c,-c))
decompose=(lambda n,l=None: (n>>i&1 for i in range(n.bit_length() if l==None else l)) if isinstance(n,Number) else chain(*n))
recompose=(lambda i: reduce(int.__or__,(k<<j for j,k in enumerate(i))))

inp=(dbg("(2+x)*3+(4*x)*6")#"(a+b)*(a+b)+0"#"((3+4-x+22-3)/3*(2+5-y+4-7)*5**4**2"#input('')
     ).replace(' ','')
digits='0123456789'
#indexes=       (  0,      1,      2,      3,   4,       5,  6,       7,  8,  9,  10,         11,       12)
prec=           (('|',), ('^',), ('&',), ('<<','>>'),  ('+','-'),   ('*','/','%','//'),      ('~',),  ('**',), ('log',))
commutativities=((True,),(True,),(True,),(False,False),(True,False),(True,False,False,False),(False,),(False,),(False,)) #with themselves
associativities=((True,),(True,),(True,),(False,False),(True,False),(True,False,False,False),(False,),(False,),(False,))
rights=         ( False,  False,  False,  False,        False,       False,                   False,   True,    False)
(ops,unc,una)=map(lambda p: tuple(decompose(p)),(prec,commutativities,associativities))
assocpairs=     (  (),     (),     (),     (),  (),      (), (),     (),  (),  (),(),          (),      (),     ())
assocpairs=tuple(starmap(lambda i,a: (i,)*a[0]+a[1],enumerate(zip(una,assocpairs))))
struc=[]
acc=''
for i in inp:
    if i in ('(',')')+ops:
        struc+=[acc]*bool(acc)+[i]
        acc=''
    else:
        acc+=i
if acc:
    struc.append(acc)
struc=list(map(lambda n: int(n) if all(map(digits.__contains__,n)) else n,struc)) #recognise ints
s=0
while s<len(struc):
    if struc[s]=='-' and isinstance(struc[s+1],Number):
        if s==0 or struc[s-1]=='(':
            del struc[s]
            struc[s]*=-1
        else:
            struc[s]='+'
            struc[s+1]*=-1
    else:
        s+=1

new=[]
no=False
for a,b in pairwise(struc):
    if no:
        no=False
    else:
        if a==b and (a=='*' or a=='/'):
            new.append(2*a)
            no=True
        else:
            new.append(a)
new.append(struc[-1])
openings=[]
closings=[]
bracks=[]
for i,n in enumerate(new):
    b=(1 if n=='(' else -1 if n==')' else 0)
    if b:
        (openings if b==1 else closings).append(i)
    bracks.append((bracks[-1] if bracks else 0)+b)

left=right=m=abs(min(bracks))
if len(openings)!=len(closings) or left:
    disp=abs(len(openings)-len(closings))
    if len(openings)>len(closings):
        right+=disp
    else:
        left+=disp
    if bracks[-1]<0:
        m+=bracks[-1]
    if left>m<right:
        m=min(left,right)-m
        left-=m
        right-=m
    openings=list(range(left))+[o+left for o in openings]
    new=['(']*left+new
    closings=[c+left for c in closings]+list(range(len(new),len(new)+right))
    new+=[')']*right
    bracks=list(range(1,left+1))+[b+left for b in bracks]+list(revange(right))
    print("attempted to fix mismatched brackets")
    print(''.join(map(str,new)))

struc=[]
i=0
inds=[0]
strucget=(lambda struc,inds: reduce(lambda a,b: a[b],inds[:-1],struc))
while i<len(new):
    if i in openings:
        strucget(struc,inds).append([])
        inds.append(0)
    else:
        if i in closings:
            del inds[-1]
        else:
            strucget(struc,inds).append(new[i])
        inds[-1]+=1
    i+=1
def structrans(struc,f=None,lf=None,rev=False,fints=False):
    inds=[len(struc)-1 if rev else 0]
    b=False
    while len(inds) and type(struc)==list and 0<=inds[0]<len(struc):
        if f:
            (struc,inds)=f(struc,inds)
        if type(strucget(struc,inds))==list:
            if lf:
                (struc,inds)=lf(struc,inds)
            inds.append(len(strucget(struc,inds+[0]))-1 if rev and type(strucget(struc,inds+[0]))==list else 0)
        else:
            del inds[-1]
            if len(inds):
                inds[-1]+=(-1)**rev
        while len(inds) and (isinstance(strucget(struc,inds),Number) or (inds[-1]<0 if rev else len(strucget(struc,inds))<=inds[-1])):
            if f and fints and isinstance(strucget(struc,inds),Number):
                (struc,inds)=f(struc,inds)
            del inds[-1]
            if not inds:
                b=True
                break
            inds[-1]+=(-1)**rev
        if len(inds) and b: break
    if f and (type(struc)==list or fints):
        struc=f(struc,[0])[0]
    if lf and type(struc)==list:
        struc=lf(struc,[0])[0]
    return(struc)

def strucset(struc,inds,val): #function call cannot be assigned to directly for whatever reason
    if len(inds)>1:
        strucget(struc,inds[:-1])[inds[-2]]=val
    else:
        struc=val
    return(struc)

def strucsert(struc,inds,nind,val): #function call cannot be assigned to directly for whatever reason
    s=strucget(struc,inds)
    s.insert(nind,val)
    return(strucset(struc,inds,s))

def lisp(struc,inds,p,o,rev=False): #my beloved
    g=strucget(struc,inds)
    if strucget(struc,inds) in o:
        if not p: #precedence 0, word function (ie. log)
            f=strucget(struc,inds)
            del strucget(struc,inds[:-1])[inds[-2]]
            strucsert(struc,inds,0,f)
            inds.append(0)
        elif strucget(struc,inds)=='~':
            operands=strucget(struc,inds[:-1])[inds[-2]:inds[-2]+2]
            del strucget(struc,inds[:-1])[inds[-2]:inds[-2]+2]
            del inds[-1]
            strucsert(struc,inds,inds[-1],operands)
            inds.append(1)
        elif not rev or inds[-2]>0:
            sub=(strucget(struc,inds) in {'-','/'}) #subtraction and division to unaries
            operands=(lambda a,f,b: (['*',a,['/',b]] if strucget(struc,inds)=='/' else ['+',a,['-',b]]) if sub else [f,a,b])(*strucget(struc,inds[:-1])[inds[-2]-1:inds[-2]+2])
            del strucget(struc,inds[:-1])[inds[-2]-1:inds[-2]+2]
            del inds[-1]
            strucsert(struc,inds,inds[-1]-1,operands)
            inds[-1]-=1
            inds.append(2)
            if sub:
                inds.append(1)
    return(struc,inds)

def unbracket(struc,inds): #not closed-form because in-place
    if len(strucget(struc,inds))==1:
        struc=strucset(struc,inds,strucget(struc,inds)[0])
        del inds[-1]
    return(struc,inds)
struc=structrans(reduce(lambda s,o: structrans(struc,lambda s,i: lisp(s,i,o[0],*o[1]),rev=o[1][1]),enumerate(zip(prec[::-1],rights[::-1])),structrans(struc,lf=unbracket)),lf=unbracket)

straction=(lambda n: "Fraction("+str(n.numerator)+","+str(n.denominator)+")" if type(n)==Fraction else str(n)) #very suspicious
def enact(struc,inds):
    global diff
    e=strucget(struc,inds)
    if type(e)==list:
        if e[0]=='-':
            if isinstance(e[1],Number):
                diff=True
                struc=strucset(struc,inds,-e[1])
        elif e[0] in ops and e[0]!='/':
            if all(map(lambda x: isinstance(x,Number),e[1:])):
                diff=True
                struc=strucset(struc,inds,eval(straction(e[1])+e[0]+straction(e[2])))
    elif type(e)==Fraction and e.denominator==1:
        diff=True
        struc=strucset(struc,inds,e.numerator)
    return(struc,inds)

def inter(struc,inds):
    if type(strucget(struc,inds))!=list:
        struc=strucset(struc,inds,1)
    return(struc,inds)

def collapse(struc,inds):
    global diff
    if all(map(lambda x: isinstance(x,Number),strucget(struc,inds))):
        diff=True
        struc=strucset(struc,inds,sum(strucget(struc,inds)))
    return(struc,inds)

def enmax(struc,f,i=None,fints=False,iints=False):
    if i:
        struc=structrans(struc,i,fints=iints)
    #print(struc)
    global diff
    diff=True
    while diff:
        diff=False
        struc=structrans(struc,f,fints=fints)
    return(struc)

cost=(lambda struc: enmax(struc,collapse,inter,False,True))
compute=(lambda struc: enmax(struc,enact,fints=True))

struc=compute(struc)

def mutate(struc,inds): #objective simplifications override all others founr prior to speed it up
    transitions=[]
    itsOver=False #we don't generate others if an identity reduction is found
    call=strucget(struc,inds)
    if type(call)==list:
        f=call[0]
        if f in ops:
            if f=='/' and call[1]==1:
                transitions=[compute(strucset(deepcopy(struc),inds,1))]
                itsOver=True
            else:
                for comm,call in (lambda c: ((0,c),(1,(lambda f,a,b: [f,b,a])(*c))) if unc[ops.index(c[0])] else ((0,c),))(call): #commutativity
                    if f=='+' and call[2]==0 or f in {'*','**'} and call[2]==1: #additive/multiplicative/divisive/exponential identities (can be removed without loss of generality)
                        transitions=[compute(strucset(deepcopy(struc),inds,call[1]))]
                        itsOver=True
                        break
                    else:
                        if f=='*':
                            if type(call[1])==list and call[1][0]=='+': #distributivity ((a+b)*c=a*c+b*c)
                                transitions.append(compute(strucset(deepcopy(struc),inds,(lambda a,b: ['+',[f,a[1],b],[f,a[2],b]])(*call[1:]))))
                            elif isinstance(call[1],Number) and type(call[2])==list and call[2][0]=='/':
                                mut=compute(strucset(deepcopy(struc),inds,Fraction(call[1],call[2][1])))
                                if any(map(lambda c: isinstance(c,Number),call[1:])) or gcd(*call[1:])==1:
                                    transitions.append(mut)
                                else:
                                    transitions=[mut]
                                    itsOver=True
                                    break
                        elif f=='+' and type(call[1])==list and call[1][0]=='*': #all(map(lambda n: type(n)==list and n[0]=='*',call[1:])) and call[1][1]==call[2][1]: #hmm
                            if type(call[2])==list and call[2][0]=='*':
                                transitions.append(compute(strucset(deepcopy(struc),inds,(lambda f,a,b: ['*',a[1],['+',a[2],b[2]]])(*call))))
                            elif call[1][1]==call[2]:
                                transitions.append(compute(strucset(deepcopy(struc),inds,(lambda f,a,b: ['*',a[1],['+',a[2],1]])(*call))))
                        if type(call[1])==list and ops.index(call[1][0]) in assocpairs[ops.index(f)]: #associativity (swapping precedence)
                            transitions.append(compute(strucset(deepcopy(struc),inds,(lambda f,a,b: [a[0],[f,a[1],b],a[2]])(*call))))
                    if comm:
                        transitions.append(compute(strucset(deepcopy(struc),inds,call)))
    elif type(call)==Fraction:
        transitions.append(compute(strucset(deepcopy(struc),inds,['*',call.numerator,['/',call.denominator]])))
    return(transitions,itsOver)

print('mutating')
def mutations(struc): # #intended to be such that all(map(lambda t: i in mutations(t),mutations(i))) is True
    (transitions,itsOver)=mutate(deepcopy(struc),[0])
    if not itsOver:
        inds=[0]
        go=False
        b=False
        while inds[0]<len(struc):
            if type(strucget(struc,inds))==list:
                inds.append(0)
                if go:
                    (newTransitions,newOver)=mutate(deepcopy(struc),inds)
                    if newOver:
                        transitions=newTransitions
                        break
                    else:
                        transitions+=newTransitions
                    go=False
            else:
                call=strucget(struc,inds)
                if type(call)==Fraction:
                    strew=deepcopy(struc)
                    transitions.append(compute(strucset(strew,inds,['*',call.numerator,['/',call.denominator]])))
                del inds[-1]
                inds[-1]+=1
            while isinstance(strucget(struc,inds),Number) or (inds[-1]>=len(strucget(struc,inds))):
                del inds[-1]
                if not inds:
                    b=True
                    break
                inds[-1]+=1
            go=True
            if b: break
    return(transitions)

states=[struc]
stateTransitions=[[]]
searcheds=[False]

dist=1
length=0
while dist<18 and length!=len(states):
    print(dist,len(states),(lambda s: (cost(deepcopy(s)),s))(min(states,key=lambda s: cost(deepcopy(s)))))
    length=len(states)
    for i,(s,e) in enumerate(zip(states[:len(states)],searcheds[:len(states)])):
        if not e:
            for m in mutations(s):
                if m in states:
                    stateTransitions[i].append(states.index(m))
                else:
                    #print('n',len(states),m)
                    states.append(m)
                    searcheds.append(False)
                    stateTransitions.append([])
                    stateTransitions[i].append(len(states)-1)
    dist+=1
#print('\n'.join(map(str,states)))
