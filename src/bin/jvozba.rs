extern crate clap;
extern crate jvozba;

use jvozba::{zbasu, Class};
use clap::{App, Arg};

fn main() {
    let args = App::new("jvozba")
        .arg(
            Arg::with_name("gismu")
                .value_name("GISMU")
                .takes_value(true)
                .required(true)
                .multiple(true),
        )
        .arg(Arg::with_name("brivla").short("b"))
        .get_matches();

    let bs = zbasu(&args.values_of("gismu").unwrap().collect::<Vec<_>>())
        .unwrap()
        .into_iter()
        .filter(|&(_, c, _)| {
            c == if args.is_present("brivla") {
                Class::Brivla
            } else {
                Class::Cmene
            }
        })
        .map(|(s, _, l)| (s, l))
        .collect::<Vec<_>>();

    for (s, w) in bs {
        println!("{}\t{}", s, w);
    }
}
