Small tool that connects a modified [https://github.com/parttimenerd/cbmc/blob/information_flow](CBMC)
with the [https://github.com/parttimenerd/relationscutter](relationscutter) tool.

It only does a bit of preprocessing and is used for testing CBMC and relationscutter together.

Usage
------------

Installation via https://python-poetry.org

.. code::

    poetry install

    # if update.sh has been called (installing the custom CBMC)
    poetry run dsharpy test.c

License
-------
MIT