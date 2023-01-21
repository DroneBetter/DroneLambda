from functools import reduce
from itertools import chain,pairwise,starmap
from copy import deepcopy
from fractions import Fraction
from numbers import Number
#print its arguments and return them (debug)
dbg=(lambda x,*s: (x,print(*s,x))[0])
#range but reversed
revange=(lambda a,b=None,c=1: range(b-c,a-c,-c) if b else range(a-c,-c,-c))
#int -> bitlist, list flattening (1 level)
decompose=(lambda n,l=None: (n>>i&1 for i in range(n.bit_length() if l==None else l)) if isinstance(n,Number) else chain(*n))
#bitlist -> int
recompose=(lambda i: reduce(int.__or__,(k<<j for j,k in enumerate(i))))

inp=(dbg("1+(6+2*x)/2)/(2)")#"(a+b)*(a+b)+0"#"((3+4-x+22-3)/3*(2+5-y+4-7)*5**4**2"#input('')
     ).replace(' ','')
digits='0123456789'
#indexes=       (  0,      1,      2,      3,   4,       5,  6,       7,  8,  9,  10,         11,       12)
#ops
prec=           (('|',), ('^',), ('&',), ('<<','>>'),  ('+','-'),   ('*','/','%','//'),      ('~',),  ('**',))
#unc - if can do AopB -> BopA
commutativities=((True,),(True,),(True,),(False,False),(True,False),(True,False,False,False),(False,),(False,)) #with themselves
#if can do AopBopC -> AopCopB
associativities=((True,),(True,),(True,),(False,False),(True,False),(True,False,False,False),(False,),(False,))
#if right-associative
rights=         ( False,  False,  False,  False,        False,       False,                   False,   True)
(ops,unc,una)=map(lambda p: tuple(decompose(p)),(prec,commutativities,associativities))
#if can do... Aop1Bop2C -> Aop2Cop1B?
assocpairs=     (  (),     (),     (),     (),  (),      (), (),     (8,),(7,),(),(),          (),      ())
assocpairs=tuple(starmap(lambda i,a: (i,)*a[0]+a[1],enumerate(zip(una,assocpairs))))
struc=[]# the expression getting manipulated
#tokenize
acc=''
for i in inp:
    if i in ('(',')')+ops:
        struc+=[acc]*bool(acc)+[i]
        acc=''
    else:
        acc+=i
if acc:
    struc.append(acc)
#recognise ints
struc=list(map(lambda n: int(n) if all(map(digits.__contains__,n)) else n,struc))
#constant-fold negation
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
#handle ** //
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
#brackets
openings=[]
closings=[]
bracks=[]
for i,n in enumerate(new):
    b=(1 if n=='(' else -1 if n==')' else 0)
    if b:
        (openings if b==1 else closings).append(i)
    bracks.append((bracks[-1] if bracks else 0)+b)

left=right=abs(min(bracks))
if len(openings)!=len(closings) or left:
    disp=abs(len(openings)-len(closings))
    if len(openings)>len(closings):
        right+=disp
    else:
        left+=disp
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
strucget=(lambda struc,inds: reduce(lambda a,b: a[b],inds[:-1],struc))#get array from a nested struc
#make nested array out of bracketing
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
print(struc)
def structrans(struc,f=None,lf=None,rev=False,fints=False):
    '''Apply f to each nested element of struc, and lf to each nested list thereof.
    struc - a possibly very nested array
    f, lf - functions: struc, inds -> (struc, inds)
    rev - bool: traverse struc backwards
    fints - bool: I don't really know what it does
    '''
    inds=[len(struc)-1 if rev else 0]
    b=False
    while 0<=inds[0]<len(struc):
        if f:
            (struc,inds)=f(struc,inds)
        if type(strucget(struc,inds))==list:
            if lf:
                (struc,inds)=lf(struc,inds)
            inds.append(len(strucget(struc,inds))-1 if rev else 0)
        else:
            del inds[-1]
            inds[-1]+=(-1)**rev
        while isinstance(strucget(struc,inds),Number) or (inds[-1]<0 if rev else len(strucget(struc,inds))<=inds[-1]):
            if f and fints and isinstance(strucget(struc,inds),Number):
                (struc,inds)=f(struc,inds)
            del inds[-1]
            if not inds:
                b=True
                break
            inds[-1]+=(-1)**rev
        if b: break
    if f:
        struc=f(struc,[0])[0]
    if lf:
        struc=lf(struc,[0])[0]
    return(struc)

def lisp(struc,inds,o,rev=False): #my beloved
    '''Convert to Lisp-style syntax:
    ['~', a, b] -> []
    '''
    if strucget(struc,inds) in o:
        if strucget(struc,inds)=='~':
            operands=strucget(struc,inds[:-1])[inds[-2]:inds[-2]+2]
            del strucget(struc,inds[:-1])[inds[-2]:inds[-2]+2]
            del inds[-1]
            strucget(struc,inds).insert(inds[-1],operands)
            inds.append(1)
        elif not rev or inds[-2]>0:
            sub=(strucget(struc,inds)=='-')
            operands=(lambda a,f,b: ['+',a,['-',b]] if sub else [f,a,b])(*strucget(struc,inds[:-1])[inds[-2]-1:inds[-2]+2])
            del strucget(struc,inds[:-1])[inds[-2]-1:inds[-2]+2]
            del inds[-1]
            strucget(struc,inds).insert(inds[-1]-1,operands)
            inds[-1]-=1
            inds.append(2)
            if sub:
                inds.append(1)
    return(struc,inds)

def setAtInd(struc,inds,val): #function call cannot be assigned to directly for whatever reason
    if len(inds)>1:
        strucget(struc,inds[:-1])[inds[-2]]=val
    else:
        struc=val
    return(struc)

def unbracket(struc,inds): #not closed-form because in-place
    if len(strucget(struc,inds))==1:
        struc=setAtInd(struc,inds,strucget(struc,inds)[0])
        del inds[-1]
    return(struc,inds)
struc=structrans(reduce(lambda s,o: structrans(struc,lambda s,i: lisp(s,i,*o),rev=o[1]),zip(prec[::-1],rights[::-1]),structrans(struc,lf=unbracket)),lf=unbracket)

straction=(lambda n: "Fraction("+str(n.numerator)+","+str(n.denominator)+")" if type(n)==Fraction else str(n)) #very suspicious
def enact(struc,inds):
    global diff
    e=strucget(struc,inds)
    if type(e)==list:
        if e[0] in ops and all(map(lambda x: isinstance(x,Number),e[1:])):
            struc=setAtInd(struc,inds,(Fraction(e[1],e[2]) if e[0]=='/' else eval(straction(e[1])+e[0]+straction(e[2]))))
            diff=True
    elif type(e)==Fraction:
        if e.denominator==1:
            struc=setAtInd(struc,inds,e.numerator)
    return(struc,inds)

def inter(struc,inds):
    if type(strucget(struc,inds))!=list:
        struc=setAtInd(struc,inds,1)
    return(struc,inds)

def collapse(struc,inds):
    global diff
    if len(inds)>1:
        if all(map(lambda x: isinstance(x,Number),strucget(struc,inds))):
            diff=True
            struc=setAtInd(struc,inds,sum(strucget(struc,inds)))
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

cost=(lambda struc: sum(enmax(struc,collapse,inter,False,True)))
compute=(lambda struc: enmax(struc,enact,fints=True))

struc=compute(struc)

def mutate(struc,inds):
    transitions=[]
    call=strucget(struc,inds)
    f=call[0]
    if f in ops:
        if unc[ops.index(f)]: #commutativity (swapping parameters)
            strew=struc
            strucget(strew,inds[:-1])[inds[-2]]=(lambda f,a,b: [f,b,a])(*call)
            #print('c',strew)
            transitions.append(compute(strew))
        if type(call[1])==list and ops.index(call[1][0]) in assocpairs[ops.index(f)]: #associativity (swapping precedence)
            strew=struc
            strucget(strew,inds[:-1])[inds[-2]]=(lambda f,a,b: [f,a[1],[f,a[2],b]])(*call)
            #print('a',strew)
            transitions.append(compute(strew))
        if f in {'*','/'} and type(call[1])==list and call[1][0]=='+': #distributivity ((a+b)*c=a*c+b*c)
            strew=struc
            strucget(strew,inds[:-1])[inds[-2]]=(lambda a,b: ['+',[f,a[1],b],[f,a[2],b]])(*call[1:])
            transitions.append(compute(strew))
        if f=='+' and call[2]==0 or f in {'*','/','**'} and call[2]==1: #additive/multiplicative/divisive/exponential identities
            strew=struc
            strucget(strew,inds[:-1])[inds[-2]]=call[1]
            transitions.append(compute(strew))
    return(transitions)
print('mutating')
def mutations(struc): # #intended to be such that all(map(lambda t: i in mutations(t),mutations(i))) is True
    transitions=[]
    inds=[0]
    go=False
    b=False
    while inds[0]<len(struc):
        if type(strucget(struc,inds))==list:
            inds.append(0)
            if go:
                if type(strucget(struc,inds))==list:
                    transitions+=mutate(deepcopy(struc),inds)
                go=False
        else:
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
while dist<12 and length!=len(states):
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
