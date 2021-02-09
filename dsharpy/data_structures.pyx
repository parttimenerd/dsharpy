# based on https://github.com/eldridgejm/unionfind/blob/master/unionfind.pyx

cimport cython
from libcpp.vector cimport vector
from libcpp.unordered_map cimport unordered_map
from libcpp cimport bool

cdef class UnionFind:
    """
    A union find implementation written in Cython based on
    https://github.com/eldridgejm/unionfind/

    Extended with `union_many`, `find_eq_classes` (obtain a list of equivalence sets)
    and `find_related`.
    Removed recursion from _find, use path splitting and vectors

    Ignores signs of numbers

    Why implement in this Cython?
    1. faster
    2. fun to try Cython
    3. useful data structures for other use cases
    """

    cdef int n_points
    cdef vector[int] parent
    cdef vector[int] rank
    cdef int _n_sets
    cdef int start

    def __cinit__(self, int n_points, int start = 0):
        self.n_points = n_points
        self.start = start
        self.parent.resize(n_points)
        self.rank.resize(n_points)

        cdef int i
        for i in range(n_points):
            self.parent[i] = i
            self.rank[i] = 1
        self._n_sets = n_points - self.start

    def valid_index(self, int i) -> bool:
        return self.start <= abs(i) < self.n_points

    def find(self, int i, bool ignore_invalid = False) -> int:
        """ Find the equivalence class for index i """
        if not self.valid_index(i):
            if ignore_invalid:
                return -1
            else:
                raise ValueError("Out of bounds index.")
        if i < 0:
            return self._find(-i)
        return self._find(i)

    def union(self, int i, int j) -> int:
        return self.union_many([i, j])

    def union_many(self, list multiple, bool ignore_invalid = False) -> int:
        """
        Build the union of multiple elements (accepts list [of lists, …] of ints), -1 if all invalid
        """

        assert len(multiple) > 0

        cdef int root_i, root_j, j, i
        root_i = -1
        i = 0
        while root_i == -1 and i < len(multiple):
            root_i = self.union_many(multiple[i], ignore_invalid) \
                if isinstance(multiple[i], list) \
                else self.find(multiple[i], ignore_invalid)
            i += 1

        for j in range(i, len(multiple)):

            root_j = self.union_many(multiple[j], ignore_invalid) \
                if isinstance(multiple[j], list) \
                else self.find(multiple[j], ignore_invalid)
            if root_j == -1:
                continue
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

    def find_related(self, list starts, list ends) -> tuple:
        """
        Returns the ends that depend on each start and the start
        equivalence classes
        """
        cdef dict d
        d = {}
        cdef vector[vector[int]] start_eqs
        cdef unordered_map[int, int] indices

        cdef int start
        for start in starts:
            root = self.find(start, True)
            if indices.find(root) == indices.end():
                indices[root] = start_eqs.size()
                start_eqs.push_back(vector[int]())
            start_eqs[indices[root]].push_back(start)

        for eq in start_eqs:
            root = self._find(eq[0])
            end = [i for i in ends if self.find(i, True) == root]
            for s in eq:
                d[s] = end
        return d, start_eqs

    def find_eq_classes(self) -> "List[List[int]]":
        """ Compute the list of equivalence classes (List[List[int]]) """
        cdef unordered_map[int, vector[int]] d
        for i in range(self.start, self.n_points):
            root = self._find(i)
            if d.find(root) == d.end():
                d[root] = set()
            d[root].push_back(i)
        return [item.second for item in d]

    def __copy__(self) -> UnionFind:
        uf = UnionFind(0)
        uf.start = self.start
        uf._n_sets = self._n_sets
        uf.n_points = self.n_points
        uf.rank = vector[int](self.rank)
        uf.parent = vector[int](self.parent)
        return uf

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

    property start:
        def __get__(self):
            return self.start

    property n_points:
        def __get__(self):
            return self.n_points
