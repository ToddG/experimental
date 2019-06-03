# Problem : Manage Dependencies

Read an input file with various commands that build a graph of dependencies, and print the result.

## Commands

* ADD       : Adds a node to the graph as a root node (e.g. it has no dependencies)
* DEP       : Make nodes as dependencies of another node
* REMOVE    : Remove a node, and it's dependendencies, from the graph, if possible
* PRINT     : Dump the graph
* SYSTEM    : Make a node a system node, and as such, it's not removable

## Input File

The following input file illustrates the commands:

```bash
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
```

## Comments

* Items can belong to multiple parents

```bash
ADD a b c z
DEP a b c
DEP z b c

>>> [
        [a] -> [[b], [c]], 
        [z] -> [[b], [c]],
    ]
```

Q: Can you remove 'c'? No.
Q: Can you remove 'b'? No.
Q: Can you remove 'a'? Yes, and that will transitively remove 'b' and 'c', but only within the 'a' subgraph

* You can only remove root level items

It seems to me, that the root level items are the only items without dependendencies. Therefore, they are the only ones that can actually be removed. This means that if an item is a root level node, and it is later made to be a dependency of another item, then it is no longer a root level node. This also means that if a node was a dependency, but that parent node is removed, then that node is removed if it's not referenced anywhere else, or if it's a system node, it's moved to the root level.

* Updating a node's dependencies updates for all instances or placements of that node

```bash
ADD a b c z q
DEP a b c
DEP z b c
DEP c q

>>> [
        [a] -> [[b], [c] -> [q]], 
        [z] -> [[b], [c] -> [q]],
    ]
```

This implies that there is only one instance of a given node to be updated. The easy way to accomplish this would be with a map. Below I'll parse the input from the lines above...


See solution.py for implementation details.
