# Problem : Manage Dependencies


## Rules

# Add items to the graph
# Items that are not dependent on something else are root nodes
# Items that are dependent on another node are child nodes
# Commands : ADD DEP REMOVE PRINT SYSTEM
# Commands to remove a node with children fail

## Input File

"""
# adds [a, b, c, d] as root level nodes
# add implies no ordering or dependencies between nodes
# added items can be removed provided that their dependency tree
#   only contains items within this tree
ADD a b c
ADD d e

# adds system items that cannot be removed
SYSTEM q

# make [b, c, d] children of a, after which only [a, e] are root nodes
# item[0] is parent of children [1..]
# children [1..] have no ordering
DEP a b c d

# make [c, d] children of [b]
DEP b c d

# removes the leaf node [d] from the parent [b]
REMOVE d

# print's an error message as this is not allowed, as [a] has children
REMOVE a

# prints error message as this is not allowed, as [z] is not present

# prints error message as graph mutations are not allowed after a REMOVE  
ADD z

# prints error message as graph mutations are not allowed after a REMOVE  
DEP c e

# dumps the final graph
# [[a] -> [[b] -> [c]], [e]]
PRINT
"""

## Comments

Though not spelled out in the problem, here are the issues that I can see with this:

* Items can belong to multiple parents

"""
ADD a b c z
DEP a b c
DEP z b c

>>> [
        [a] -> [[b], [c]], 
        [z] -> [[b], [c]],
    ]
"""

Q: Can you remove c? No.
Q: Can you remove b? No.
Q: Can you remove a? Yes, and transitively b and c, but only within the a subgraph

* You can only remove root level items

It seems to me, that the root level items are the only items without dependendencies. Therefore, they are the only ones that can actually be removed. This means that if an item is a root level node, and it is later made to be a dependency of another item, then it is no longer a root level node.

* Updating a node's dependencies updates for all instances or placements of that node

"""
ADD a b c z q
DEP a b c
DEP z b c
DEP c q

>>> [
        [a] -> [[b], [c] -> [q]], 
        [z] -> [[b], [c] -> [q]],
    ]
"""

This implies that there is only one instance of a given node to be updated. The easy way to accomplish this would be with a map. Below I'll parse the input from the lines above...

# python
```
from sets import Set
class Node:
    """
    Reference parents and children by name.
    """
    def __init__(self, name):
        self._name = name
        self._parents = Set([])
        self._children = Set([])

    def add_parent(self, parent):
        self._parents.add(parent)

    def add_children(self, children):
        for child in children:
            self._children.add(child)

# create the graph (as a map)
g = {}

# Manually, parse the input
# Nodes default to the root level, with no parents or children
# ADD a b c z q 
g['a']=Node('a')
g['b']=Node('b')
g['c']=Node('c')
g['z']=Node('z')
g['q']=Node('q')

# Build the graph relationships with the DEP statements
# DEP a b c
g['a'].children.append(['b', 'c'])
g['b'].parent.append('a')
g['c'].parent.append('a')

# DEP z b c
g['z'].children.append(['b', 'c'])
g['b'].parent.append('z')
g['c'].parent.append('z')

"""]
