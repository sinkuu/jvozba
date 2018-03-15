#![feature(slice_patterns)]

extern crate itertools;
#[macro_use]
extern crate lazy_static;
extern crate serde_json;

use serde_json::Value;
use std::str::FromStr;
use itertools::Itertools;
// use std::error::Error as StdError;
// use std::fmt;

lazy_static! {
    static ref JSON: Value = {
        Value::from_str(include_str!("../parsed-en.json")).unwrap()
    };
}

#[derive(Debug)]
pub enum Error {
    NotTanru,
    NotFound(String),
    BrokenDictionary(String),
}

// impl StdError for Error {
//     fn description(&self) -> &str {
//         "jvozba error"
//     }

//     fn cause(&self) -> Option<&StdError> {
//         None
//     }
// }

// impl fmt::Display for Error {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         writeln!(f, "{:?}", self)
//     }
// }

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Class {
    Brivla,
    Cmene,
}

pub fn zbasu(tanru: &[&str]) -> Result<Vec<(u32, Class, String)>, Error> {
    let rafsi = tanru
        .iter()
        .map(|v| {
            Ok(
                JSON.get(v)
                    .ok_or(Error::NotFound(v.to_string()))?
                    .get("r")
                    .ok_or(Error::BrokenDictionary(v.to_string()))?
                    .as_array().ok_or(Error::BrokenDictionary(v.to_string()))?
                    .into_iter()
                    .map(|v| v.as_str().unwrap().to_string())
                    .collect::<Vec<String>>(),
            )
        })
        .collect::<Result<Vec<_>, Error>>()?;

    zbasu_from_rafsi(rafsi.as_slice())
}

pub fn zbasu_from_rafsi<T, U, V>(rafsi: T) -> Result<Vec<(u32, Class, String)>, Error>
where
    T: AsRef<[U]>,
    U: AsRef<[V]>,
    V: AsRef<str>,
{
    let rafsi = rafsi.as_ref();

    if rafsi.len() == 1 {
        return Err(Error::NotTanru);
    }

    let combinations: Vec<usize> = (0..rafsi.len() + 1)
        .map(|i| rafsi[..i].iter().map(|r| r.as_ref().len()).product())
        .collect();
    let mut generated = vec![];

    'comb: for i in 0..combinations[rafsi.len()] {
        let mut rs = vec![];
        let mut rafsi_score = 0;
        let mut class = Class::Brivla;

        for j in 0..rafsi.len() {
            let idx = (i / combinations[j]) % rafsi[j].as_ref().len();
            let e: &str = rafsi[j].as_ref()[idx].as_ref();
            let len = e.chars().filter(|&c| c != '\'').count();
            if len == 5 && j != rafsi.len() - 1 {
                continue 'comb;
            }
            if len == 4 && j == rafsi.len() - 1 {
                class = Class::Cmene;
            }
            rafsi_score += score_rafsi(e);
            rs.push(e);
        }

        let mut lujvo = String::new();
        let mut num_hyphens = 0;
        let (rs, mut first_cvc) = if is_cvv(rs[0]) && (rs.len() > 2 || !is_ccv(rs[1])) {
            lujvo.push_str(rs[0]);
            lujvo.push(if rs[1].starts_with('r') { 'n' } else { 'r' });
            num_hyphens += 1;
            (&rs[1..], false)
        } else {
            (&rs[..], true)
        };
        let mut first_joint = None;
        for (a, b) in rs.iter().tuple_windows() {
            lujvo.push_str(a);
            if !is_cvc(a) {
                first_cvc = false;
            }
            let ac = a.chars().last().unwrap();
            let bc = b.chars().next().unwrap();
            if is_consonant(ac) && is_consonant(bc)
                && (is_impermissible_consonant_pairs(ac, bc)
                    || a.chars().filter(|&c| c != '\'').count() == 4)
            {
                lujvo.push('y');
                num_hyphens += 1;
                first_cvc = false;
            } else if first_cvc && (is_cvc(b) || is_cvccv(b)) {
                if is_permissible_initial_consonant_pairs(ac, bc) {
                    if first_joint.is_none() {
                        first_joint = Some(lujvo.len());
                    }
                } else {
                    first_joint = None;
                    first_cvc = false;
                }
            }
        }

        lujvo.push_str(&rs[rs.len() - 1]);

        if let Some(first_joint) = first_joint {
            lujvo.insert(first_joint, 'y');
            num_hyphens += 1;
        }

        if !is_brivla(&lujvo) {
            class = Class::Cmene;
        }

        generated.push((lujvo, class, num_hyphens, rafsi_score));
    }

    let mut generated: Vec<_> = generated
        .into_iter()
        .map(|(lujvo, class, h, r)| {
            let l = lujvo.len() as u32;
            let a = lujvo.chars().filter(|&c| c == '\'').count() as u32;
            let v = lujvo
                .chars()
                .filter(|&c| c != 'y')
                .filter(|&c| is_vowel(c))
                .count() as u32;
            (
                (1000 * l) - (500 * a) + (100 * h) - (10 * r) - v,
                class,
                lujvo,
            )
        })
        .collect();

    generated.sort_by_key(|&(s, _, _)| s);

    Ok(generated)
}

pub fn zbasu_best(class: Class, tanru: &[&str]) -> Result<String, Error> {
    Ok(zbasu(tanru)?
        .into_iter()
        .filter(|&(_, c, _)| c == class)
        .map(|(_, _, l)| l)
        .next()
        .unwrap())
}

#[test]
fn test_zbasu() {
    assert_eq!(
        zbasu_from_rafsi([["tos"], ["mabru"]]).unwrap()[0].2,
        "tosymabru"
    );
    assert_eq!(zbasu_from_rafsi([["sai"], ["cli"]]).unwrap()[0].2, "saicli");

    use Class::*;

    assert_eq!(
        zbasu(&["re", "xislu", "marce"]).unwrap(),
        [
            (9336, Brivla, "relxilma\'e".to_string()),
            (9825, Brivla, "relxi\'uma\'e".to_string()),
            (9877, Cmene, "relxilmarc".to_string()),
            (10366, Cmene, "relxi\'umarc".to_string()),
            (10886, Brivla, "relxilmarce".to_string()),
            (11375, Brivla, "relxi\'umarce".to_string()),
            (11466, Brivla, "relxislyma\'e".to_string()),
            (12007, Cmene, "relxislymarc".to_string()),
            (13016, Brivla, "relxislymarce".to_string()),
        ],
    );
    assert_eq!(
        zbasu(&["mlatu", "cmalu", "tcadu"]).unwrap(),
        &[
            (8807, Brivla, "latcmatca".to_string()),
            (9837, Cmene, "latcmatcad".to_string()),
            (10846, Brivla, "latcmatcadu".to_string()),
            (10917, Brivla, "mlatycmatca".to_string()),
            (10937, Brivla, "latcmalytca".to_string()),
            (11947, Cmene, "mlatycmatcad".to_string()),
            (11967, Cmene, "latcmalytcad".to_string()),
            (12956, Brivla, "mlatycmatcadu".to_string()),
            (12976, Brivla, "latcmalytcadu".to_string()),
            (13047, Brivla, "mlatycmalytca".to_string()),
            (14077, Cmene, "mlatycmalytcad".to_string()),
            (15086, Brivla, "mlatycmalytcadu".to_string()),
        ],
    );

    assert_eq!(zbasu_best(Brivla, &["lerfu", "liste"]).unwrap(), "lerste",);
    assert_eq!(zbasu_best(Brivla, &["skami", "pilno"]).unwrap(), "sampli",);
    assert_eq!(zbasu_best(Brivla, &["skami", "pilno"]).unwrap(), "sampli",);
    assert_eq!(
        zbasu_best(Brivla, &["pu'u", "re", "linji", "julne"]).unwrap(),
        "puvyrelyli\'iju\'e",
    );
    assert_eq!(
        zbasu_best(
            Brivla,
            &[
                "carna", "ke", "kalsa", "gasnu", "ke'e", "bliku", "ke", "kelci", "tutci"
            ]
        ).unwrap(),
        "carkemkasygauke\'eblikemkeitci",
    );
    assert_eq!(
        zbasu_best(Cmene, &["blanu", "kanla", "mlatu"],).unwrap(),
        "blakalmlat",
    );
}

fn score_rafsi(r: &str) -> u32 {
    if r.find('\'').is_some() {
        // CVV
        if r.chars()
            .filter(|&c| c != '\'')
            .map(is_consonant)
            .eq([true, false, false].iter().cloned())
        {
            return 6;
        }
    }
    let cs = r.chars().map(is_consonant).collect::<Vec<_>>();
    match *cs {
        // CVCCV
        [true, false, true, true, false] => 1,
        // CVCC
        [true, false, true, true] => 2,
        // CCVCV
        [true, true, false, true, false] => 3,
        // CCVC
        [true, true, false, true] => 4,
        // CVC
        [true, false, true] => 5,
        // CCV
        [true, true, false] => 7,
        // CVV with no apostrophe
        [true, false, false] => 8,
        _ => panic!("invalid rafsi: {}", r),
    }
}

#[test]
fn test_score_rafsi() {
    assert_eq!(score_rafsi("sarji"), 1);
    assert_eq!(score_rafsi("sarj"), 2);
    assert_eq!(score_rafsi("zbasu"), 3);
    assert_eq!(score_rafsi("zbas"), 4);
    assert_eq!(score_rafsi("nun"), 5);
    assert_eq!(score_rafsi("ta'u"), 6);
    assert_eq!(score_rafsi("zba"), 7);
    assert_eq!(score_rafsi("sai"), 8);
}

fn is_consonant(c: char) -> bool {
    match c {
        'p' | 'b' | 'f' | 'v' | 't' | 'd' | 's' | 'z' | 'c' | 'j' | 'k' | 'g' | 'x' | 'm' | 'n'
        | 'r' | 'l' | '\'' => true,
        _ => false,
    }
}

fn is_vowel(c: char) -> bool {
    match c {
        'a' | 'e' | 'i' | 'o' | 'u' => true,
        _ => false,
    }
}

fn is_cvv(rafsi: &str) -> bool {
    if !(rafsi.len() == 3 || rafsi.len() == 4) {
        return false;
    }

    let rafsi = rafsi.as_bytes();

    if is_consonant(rafsi[0] as char) && is_vowel(rafsi[1] as char) {
        (rafsi[2] == b'\'' && is_vowel(rafsi[3] as char)) || is_vowel(rafsi[2] as char)
    } else {
        false
    }
}

fn is_ccv(rafsi: &str) -> bool {
    if rafsi.len() != 3 {
        return false;
    }

    let rafsi = rafsi.as_bytes();
    is_consonant(rafsi[0] as char) && is_consonant(rafsi[1] as char) && is_vowel(rafsi[2] as char)
}

fn is_cvc(rafsi: &str) -> bool {
    if rafsi.len() != 3 {
        return false;
    }

    let rafsi = rafsi.as_bytes();
    is_consonant(rafsi[0] as char) && is_vowel(rafsi[1] as char) && is_consonant(rafsi[2] as char)
}

fn is_cvccv(rafsi: &str) -> bool {
    if rafsi.len() != 5 {
        return false;
    }

    let rafsi = rafsi.as_bytes();
    is_consonant(rafsi[0] as char) && is_vowel(rafsi[1] as char) && is_consonant(rafsi[2] as char)
        && is_consonant(rafsi[3] as char) && is_vowel(rafsi[4] as char)
        && is_permissible_initial_consonant_pairs(rafsi[2] as char, rafsi[3] as char)
}

fn is_permissible_initial_consonant_pairs(a: char, b: char) -> bool {
    #[cfg_attr(rustfmt, rustfmt_skip)]
    match (a, b) {
        ('b', 'l') | ('b', 'r') |
        ('c', 'f') | ('c', 'k') | ('c', 'l') | ('c', 'm') | ('c', 'n') | ('c', 'p') | ('c', 'r') | ('c', 't') |
        ('d', 'j') | ('d', 'r') | ('d', 'z') |
        ('f', 'l') | ('f', 'r') |
        ('g', 'l') | ('g', 'r') |
        ('j', 'b') | ('j', 'd') | ('j', 'g') | ('j', 'm') | ('j', 'v') |
        ('k', 'l') | ('k', 'r') |
        ('m', 'l') | ('m', 'r') |
        ('p', 'l') | ('p', 'r') |
        ('s', 'f') | ('s', 'k') | ('s', 'l') | ('s', 'm') | ('s', 'n') | ('s', 'p') | ('s', 'r') | ('s', 't') |
        ('t', 'c') | ('t', 'r') | ('t', 's') |
        ('v', 'l') | ('v', 'r') |
        ('x', 'l') | ('x', 'r') |
        ('z', 'b') | ('z', 'd') | ('z', 'g') | ('z', 'm') | ('z', 'v') => true,
        _ => false,
    }
}

fn is_impermissible_consonant_pairs(a: char, b: char) -> bool {
    if is_vowel(a) || is_vowel(b) {
        return false;
    }

    if a == b {
        return true;
    }

    let is_unvoiced_consonant = |c| match c {
        'p' | 't' | 'k' | 'f' | 'c' | 's' | 'x' => true,
        _ => false,
    };

    let is_voiced_consonant = |c| match c {
        'b' | 'd' | 'g' | 'v' | 'j' | 'z' => true,
        _ => false,
    };
    if (is_unvoiced_consonant(a) && is_voiced_consonant(b))
        || (is_voiced_consonant(a) && is_unvoiced_consonant(b))
    {
        return true;
    }

    let cjsz = |c| match c {
        'c' | 'j' | 's' | 'z' => true,
        _ => false,
    };
    if cjsz(a) && cjsz(b) {
        return true;
    }

    match (a, b) {
        ('c', 'x') | ('k', 'x') | ('x', 'c') | ('x', 'k') | ('m', 'z') => true,
        _ => false,
    }
}

#[test]
fn test_consonant_pairs() {
    assert!(
        !is_impermissible_consonant_pairs('s', 'm')
            && is_permissible_initial_consonant_pairs('s', 'm')
    );
    assert!(is_cvv("le\'u"));
    assert!(!is_cvv("liste"));
}

fn is_brivla(s: &str) -> bool {
    is_vowel(s.chars().last().unwrap())
        && s.chars()
            .filter(|&c| c != 'y' && c != '\'')
            .take(5)
            .tuple_windows::<(_, _)>()
            .any(|(a, b)| is_consonant(a) && is_consonant(b))
}
