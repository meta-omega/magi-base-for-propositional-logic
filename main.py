from collections import deque

class Formula:
    def __init__(self, t, children, text):
        self.symbol = t
        self.children = children
        self.text = text

    def updateText(self):
        self.text = self.toText()

    def toText(self):
        if len(self.children) == 0:
            r = self.symbol
        else:
            r = self.symbol + '('
            for i in range(len(self.children) - 1):
                r += self.children[i].toText() + ','
            r += self.children[-1].toText() + ')'
        return r

    def toTree(self):
        self.children.clear()
        self.symbol = ''
        if len(self.text) > 0:
            i = 0
            while i < len(self.text) and self.text[i] != '(':
                i += 1
            if i == len(self.text):
                self.symbol = self.text
            else:
                self.symbol = self.text[:i]
                while i < len(self.text) - 1:
                    m = i + 1
                    i = m
                    parenthesis = 0
                    goOn = True
                    while goOn:
                        i += 1
                        if self.text[i] == '(':
                            parenthesis += 1
                        elif self.text[i] == ')':
                            parenthesis -= 1

                        if parenthesis < 0:
                            goOn = False
                        elif parenthesis == 0 and self.text[i] == ',':
                            goOn = False
                    s = (self.text[m:])[:i-m]
                    self.children.append(Formula('', [], s))
                    self.children[-1].toTree()

class GraphNode:
    def __init__(self, name):
        self.name = name
        self.arrowsTo = [] # lista de otros GraphNode a los que apunta.
        self.loops = 'no idea'

class DGraph:
    def __init__(self, nodes):
        self.nodes = nodes
        self.isOrphan = {}
        self.findOrphans()

    def findOrphans(self):
        self.isOrphan = {}
        for k in self.nodes:
            self.isOrphan[k] = True
        for k in self.nodes:
            for ar in self.nodes[k].arrowsTo:
                self.isOrphan[ar.name] = False

    def hasLoops(self):
        ancestors_per_node = dict(map(lambda y: (y, set()), self.nodes))

        f = lambda x: self.isOrphan[x]
        orphans = list(filter(f, list(self.isOrphan)))

        if len(self.nodes) == 0:
            return False
        elif len(orphans) == 0:
            return True

        to_visit = deque(orphans)

        while len(to_visit) > 0:
            parent = self.nodes[to_visit.popleft()]

            for child in parent.arrowsTo:
                if child.name in ancestors_per_node[child.name]:
                    return True

                ancestors_per_node[child.name].add(parent.name)
                ancestors_per_node[child.name].update(ancestors_per_node[parent.name])
                to_visit.append(child.name)

        return False

class ProofState:
    def __init__(self):
        self.assumptions = []
        self.formulas = []
        self.nextsStates = []
        self.previousState = 'nadap'

class Rule:
    def __init__(self, name, premises, conclusion):
        self.name = name
        self.premises = premises
        self.conclusion = conclusion

def feetea(f, a, S): #determina si se puede meter cosas adentro de f (en las variables que empiezan con caracter en S) para llegar a a.
    aAndpList(f, S)
    aAndpListAux(a, S)
    buildTheGraph(S)
    #chequeo si no quedo con loops
    #rellenar vacion con nuevas a_i
    #masticar
    return feeteaAux(f, a, S)

def feeteaAux(f, a, S):
    if not f.symbol[0] in S:
        if not a.symbol[0] in S:
            if not f.symbol == a.symbol:
                #print('casito 1')
                return False
            else:
                for i in range(len(f.children)):
                    if feeteaAux(f.children[i], a.children[i], S) == False:
                        return False
                #chequear loops (o al final?) antes de returnear True
                return True
        else:
            if extension[a.symbol] == []:
                extension[a.symbol].append(f)
                return True
            else:
                return feeteaAux(f, extension[a][0])
    else:
        if not a.symbol[0] in S:
            if extension[f.symbol] == []:
                extension[f.symbol].append(a)
                return True
            else:
                return feeteaAux(a, extension[f][0])
        else:
            if f.symbol == a.symbol:
                return True
            else:
                if extension[f.symbol] == [] and extension[a.symbol] == []:
                    if f.symbol == sorted([f.symbol, a.symbol])[0]:
                        extension[f.symbol].append(a)
                        return True
                    else:
                        extension[a.symbol].append(f)
                        return True
                elif not extension[f.symbol] == [] and extension[a.symbol] == []:
                    extension[a.symbol].append(f)
                elif extension[f.symbol] == [] and not extension[a.symbol] == []:
                    extension[f.symbol].append(a)
                else:
                    return feeteaAux(extension[f.symbol], extension[a.symbol])

def aAndpList(f, S): #dada una formula f devuelve la lista de todas las variables que ocurren (? en f y empiezan con un caracter en S (generalmente S es ['a', 'p']).
    global extension
    extension = {}
    aAndpListAux(f, S)
    return extension

def aAndpListAux(f, S):
    if f.symbol[0] in S:
        if not f.symbol in extension:
            extension[f.symbol] = []
    for ch in f.children:
        aAndpListAux(ch, S)

def buildTheGraph(S):
    global G
    global d
    d = {}
    for k in extension:
        if not extension[k] == []:
            d[k] = GraphNode(k)
            global l
            l = []
            buildTheGraphAux(extension[k][0], S)
            d[k].arrowsTo = l.copy()
    print('d:', d)
    G = DGraph(d)

def buildTheGraphAux(N, S):
    if N.symbol[0] in S and N.symbol in d and not d[N.symbol] in l:
        l.append(d[N.symbol])
    for ch in N.children:
        buildTheGraphAux(ch, S)

f = Formula('^', [], '')
f.children.append(Formula('A', [], ''))
f.children.append(Formula('B', [], ''))
f.updateText()

f2 = Formula('->', [], '')
f2.children.append(Formula('a0', [], ''))
f2.children.append(Formula('a1', [], ''))
f2.updateText()
# print(f2.text)

f3 = Formula('V', [], '')
f3.children.append(Formula('^', [], ''))
f3.children.append(Formula('a1', [], ''))
f3.children[0].children.append(Formula('A', [], ''))
f3.children[0].children.append(Formula('B', [], ''))
f3.updateText()

ps = ProofState()
ps.assumptions.append(f)
ps.formulas.append(f)

ps2 = ProofState()
ps2.assumptions.append(f2)
ps2.formulas.append(f2)
ps2.previousState = ps

t1= Formula('A1', [], '')
t1.updateText()

t2= Formula('A2', [], '')
t1.updateText()

t3 = Formula('', [], '^(A1,-->(A2,A3))')
t3.toTree()

t4 = Formula('', [], '^(a1,-->(a2,a3))')
t4.toTree()

t5 = Formula('', [], '^(p1,-->(p2,p3))')
t5.toTree()

t6 = Formula('', [], '-->(V(p1,p2),-->(p2,p3))')
t6.toTree()

t7 = Formula('', [], '-->(a1,-->(-->(A1,A2),a1))')
t7.toTree()

t8 = Formula('', [], 'a1')
t8.toTree()

t9 = Formula('', [], 'a2')
t9.toTree()

t10 = Formula('', [], '-->(a1,a2)')
t10.toTree()

t11 = Formula('', [], '-->(a2,a3)')
t11.toTree()

t12 = Formula('', [], '-->(a2,a1)')
t12.toTree()

t13 = Formula('', [], '-->(-->(a2,a1),-->(a4,a3))')
t13.toTree()

t14 = Formula('', [], '-->(-->(a4,a3),-->(a1,a2))')
t14.toTree()

t15 = Formula('', [], '-->(A2,A1)')
t15.toTree()

t16 = Formula('', [], 'V(A2,A1)')
t16.toTree()

n1 = GraphNode('n1')
n2 = GraphNode('n2')
n3 = GraphNode('n3')
n4 = GraphNode('n4')

n1.arrowsTo.append(n2)
n2.arrowsTo.append(n3)
n3.arrowsTo.append(n4)

gr = DGraph({'n1': n1,'n2': n2, 'n3': n3, 'n4': n4})
print(gr.hasLoops())
