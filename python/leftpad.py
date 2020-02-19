def leftpad(char: str, length: int, string: str) -> str:
    """Left-pad the input `string` to `length` by padding with `char`.

    This implementation is verified against the pre- and post-conditions below
    using symbolic execution with CrossHair (https://github.com/pschanely/CrossHair/).
    You can run `pip install crosshair && crosshair check leftpad.py` to confirm.

    pre:
        len(char) == 1
        length >= 0
    post:
        len(__return__) == max(length, len(string))
        __return__.endswith(__old__.string)
        __return__.startswith(char * max(0, length - len(string)))
    """
    while len(string) < length:
        string = char + string
    return string
