import pytest

from dsharpy.util import process


def test_process_invalid_code():
    with pytest.raises(BaseException):
        process("""
        void main()
        {
          int __out = non;_det();
          assert(__out);
        }
        """)
