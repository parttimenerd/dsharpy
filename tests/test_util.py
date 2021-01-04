import pytest

from dsharpy.formula import DCNF
from dsharpy.util import empty, process_code_with_cbmc


def test_empty():
    assert empty([])
    assert not empty([1])


def test_process_invalid_code():
    with pytest.raises(BaseException):
        DCNF.load_string(process_code_with_cbmc("""
        void main()
        {
          int __out = non;_det();
          assert(__out);
        }
        """, preprocess=True))


def test_process_code():
    dcnf = DCNF.load_string(process_code_with_cbmc("""
void main()
{
  int __out = non_det();
  assert(__out);
}
""", preprocess=True))
    assert len(dcnf.ind) == 32
