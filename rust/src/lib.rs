use contracts::ensures;
use mirai_annotations::*;

#[ensures(s.len() >= len -> s == ret.as_slice(),
          "If s is already long enough, the result should be the same")]
#[ensures(s.len() < len -> ret.len() == len, "If padding happens, the new length is len")]
#[ensures(ret.ends_with(s), "The result always ends with s")]
#[ensures(s.len() < len -> ret.starts_with(vec![byte; len - s.len()].as_slice()),
          "Enough characters at the start are the padding byte")]
pub fn leftpad(s: &[u8], len: usize, byte: u8) -> Vec<u8> {
	if s.len() >= len {
		Vec::from(s)
	} else {
		[vec![byte; len - s.len()], s.to_vec()].concat()
	}
}

#[cfg(test)]
mod tests {
	use super::leftpad;
	#[test]
	fn no_op() {
		leftpad(b"foo", 3, b'!');
	}
	#[test]
	fn zero_len() {
		leftpad(b"foo", 0, b'!');
	}
	#[test]
	fn padded() {
		leftpad(b"foo", 5, b'!');
	}
}