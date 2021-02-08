# based on https://github.com/eldridgejm/unionfind/blob/master/unionfind.pyx

cimport cython
from libc.stdlib cimport malloc, free
from libcpp.vector cimport vector
from libcpp.unordered_map cimport unordered_map

cdef class UnionFind:
    """
    A union find implementation written in Cython based on
    https://github.com/eldridgejm/unionfind/

    Extended with `union_many` and `eq_classes` (obtain a list of equivalence sets)
    Removed recursion from _find and used path splitting
    """

    cdef int n_points
    cdef int *parent
    cdef int *rank
    cdef int _n_sets

    def __cinit__(self, int n_points):
        self.n_points = n_points
        self.parent = <int *> malloc(n_points * sizeof(int))
        self.rank = <int *> malloc(n_points * sizeof(int))

        cdef int i
        for i in range(n_points):
            self.parent[i] = i

        self._n_sets = n_points

    def find(self, int i) -> int:
        """ Find the equivalence class for index i """
        if (i < 0) or (i > self.n_points):
            raise ValueError("Out of bounds index.")
        return self._find(i)

    def union(self, int i, int j):
        if (i < 0) or (i > self.n_points) or (j < 0) or (j > self.n_points):
            raise ValueError("Out of bounds index.")

        cdef int root_i, root_j
        root_i = self._find(i)
        root_j = self._find(j)
        if root_i != root_j:
            self._n_sets -= 1
            if self.rank[root_i] < self.rank[root_j]:
                self.parent[root_i] = root_j
                return root_j
            elif self.rank[root_i] > self.rank[root_j]:
                self.parent[root_j] = root_i
                return root_i
            else:
                self.parent[root_i] = root_j
                self.rank[root_j] += 1
                return root_j
        else:
            return root_i

    def union_many(self, list multiple) -> int:
        """ Build the union of multiple elements """
        assert len(multiple) > 0

        cdef int root_i, root_j
        root_i = self.find(multiple[0])

        for j in multiple[1:]:

            root_j = self._find(j)

            if root_i != root_j:
                self._n_sets -= 1
                if self.rank[root_i] < self.rank[root_j]:
                    self.parent[root_i] = root_j
                    root_i = root_j
                elif self.rank[root_i] > self.rank[root_j]:
                    self.parent[root_j] = root_i
                else:
                    self.parent[root_i] = root_j
                    self.rank[root_j] += 1
                    root_i = root_j
        return root_i

    def __dealloc__(self):
        free(self.parent)
        free(self.rank)

    cdef int _find(self, int i):
        """ without range checks """
        # uses path halving by Tarjan (see https://en.wikipedia.org/wiki/Disjoint-set_data_structure)
        while self.parent[i] != i:
            par = self.parent[i]
            i, self.parent[i] = par, self.parent[par]
        return i

    property n_sets:
        def __get__(self):
            return self._n_sets

    property eq_classes:
        def __get__(self) -> "List[List[int]]":
            cdef unordered_map[int, vector[int]] d
            for i in range(self.n_points):
                root = self._find(i)
                if d.find(root) == d.end():
                    d[root] = set()
                d[root].push_back(i)
            return [set(item.second) for item in d]

