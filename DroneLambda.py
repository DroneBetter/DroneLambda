from functools import reduce
from itertools import chain,pairwise,starmap
from copy import deepcopy
from fractions import Fraction
from numbers import Number
dbg=(lambda x,*s: (x,print(*s,x))[0]) #debug
decompose=(lambda n,l=None: (n>>i&1 for i in range(n.bit_length() if l==None else l)) if isinstance(n,Number) else chain(*n))
recompose=(lambda i: reduce(int.__or__,(k<<j for j,k in enumerate(i))))

inp=(dbg("(3+4-x+22-3)/3*(2+5-y+4-7)*5**4**2")#input('')
     ).replace(' ','')
digits='0123456789'
#indexes=       (  0,      1,      2,      3,   4,       5,  6,       7,  8,  9,  10,         11,       12)
prec=           (('|',), ('^',), ('&',), ('<<','>>'),  ('+','-'),   ('*','/','%','//'),      ('~',),  ('**',))
commutativities=((True,),(True,),(True,),(False,False),(True,False),(True,False,False,False),(False,),(False,)) #with themselves
associativities=((True,),(True,),(True,),(False,False),(True,False),(True,False,False,False),(False,),(False,))
rights=         ( False,  False,  False,  False,        False,       False,                   False,   True)
(ops,unc,una)=map(lambda p: tuple(decompose(p)),(prec,commutativities,associativities))
assocpairs=     (  (),     (),     (),     (),  (),      (), (),     (8,),(7,),(),(),          (),      ())
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
print(struc)
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

print(struc)
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
    b=(n in {'(',')'})*(-1)**(n==')')
    if b:
        (openings if b==1 else closings).append(i)
    bracks.append((bracks[-1] if bracks else 0)+b)
if len(openings)!=len(closings) or -1 in bracks:
    print('brackets incorrect')
    exit()
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
print(struc)
def structrans(struc,f=None,lf=None,rev=False,fints=False):
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
    return(struc)

def lisp(struc,inds,o,rev=False): #my beloved
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
struc=reduce(lambda s,o: structrans(struc,lambda s,i: lisp(s,i,*o),rev=o[1]),zip(prec[::-1],rights[::-1]),struc)
def unbracket(struc,inds): #not closed-form because in-place
    if len(strucget(struc,inds))==1:
        strucget(struc,inds)[:]=strucget(struc,inds)[0]
    return(struc,inds)
structrans(struc,lf=unbracket)

straction=(lambda n: "Fraction("+str(n.numerator)+","+str(n.denominator)+")" if type(n)==Fraction else str(n)) #very suspicious
def enact(struc,inds):
    global diff
    e=strucget(struc,inds)
    if type(e)==list:
        if e[0] in ops and all(map(lambda x: isinstance(x,Number),e[1:])):
            strucget(struc,inds[:-1])[inds[-2]]=(Fraction(e[1],e[2]) if e[0]=='/' else eval(straction(e[1])+e[0]+straction(e[2])))
            diff=True
    return(struc,inds)

def inter(struc,inds):
    if type(strucget(struc,inds))!=list:
        strucget(struc,inds[:-1])[inds[-2]]=1
    return(struc,inds)

def collapse(struc,inds):
    global diff
    if len(inds)>1:
        if all(map(lambda x: isinstance(x,Number),strucget(struc,inds))):
            diff=True
            strucget(struc,inds[:-1])[inds[-2]]=sum(strucget(struc,inds))
    return(struc,inds)

def enmax(struc,f,i=None,fints=False):
    if i:
        struc=structrans(struc,i,fints=fints)
    #print(struc)
    global diff
    diff=True
    while diff:
        diff=False
        struc=structrans(struc,f)
    return(struc)

cost=(lambda struc: sum(enmax(struc,collapse,inter,True)))

struc=enmax(struc,enact)

def mutate(struc,inds):
    transitions=[]
    f=strucget(struc,inds)[0]
    if f in ops:
        strew=struc
        if unc[ops.index(f)]:
            strucget(strew,inds[:-1])[inds[-2]]=(lambda f,a,b: [f,b,a])(*strucget(strew,inds))
            #print('c',strew)
            transitions.append(strew)
        strew=struc
        #print(strucget(strew,inds))
        if type(strucget(strew,inds)[1])==list and ops.index(strucget(strew,inds)[1][0]) in assocpairs[ops.index(f)]:
            strucget(strew,inds[:-1])[inds[-2]]=(lambda f,a,b: [f,[f,b,a[2]],a[1]])(*strucget(strew,inds))
            #print('a',strew)
            transitions.append(strew)
        if f in {'*','/'} and type(strucget(strew,inds)[1])==list and strucget(strew,inds)[1][0]=='+':
            strucget(strew,inds[:-1])[inds[-2]]=(lambda a,b: ['+',[f,a[1],b],[f,a[2],b]])(*strucget(strew,inds)[1:])
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
                    transitions+=mutate(struc[:],inds)
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
            for m in mutations(s)+[enmax(deepcopy(s),enact)]:
                if m in states:
                    stateTransitions[i].append(states.index(m))
                else:
                    #print('n',len(states),m)
                    states.append(m)
                    searcheds.append(False)
                    stateTransitions.append([])
                    stateTransitions[i].append(len(states)-1)
    dist+=1
