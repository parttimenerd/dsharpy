import pytest

from dsharpy.loop_tree import ApplicableCNF, NameMapping


class TestApplicableCNF:

    app = ApplicableCNF(input=NameMapping({"in": [1, 2]}),
                        output=NameMapping({"out": [5, 6]}),
                        clauses=[[1, 3], [3, 5, 6]],
                        misc_vars=NameMapping({"misc": [3]}))


    def test_incompatible_mapping(self):
        with pytest.raises(AssertionError):
            self.app.apply(1, NameMapping({"in": [7, 8, 9]}), None)

    def test_transpose(self):
        res = self.app.transpose(10, keep=[1, 2], custom_mapping={})
        assert res.input == self.app.input
        assert res.output["out"] == [11, 12]
        assert res.clauses == [[1, 10], [10, 11, 12]]
        assert res.misc_vars["misc"] == [10]

    def test_apply(self):
        res = self.app.apply(10, NameMapping({"in": [7, 8]}), output=None)
        assert res.output["out"] == [11, 12]
        assert res.input["in"] == [7, 8]
