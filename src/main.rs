use toml::Table;
use z3::{
    Solver,
    ast::{Bool, atleast, atmost},
};

const BIOMES: &str = include_str!("../examples/biomes.toml");

#[derive(Debug)]
struct Data {
    names: Vec<String>,
    props: Vec<(String, Vec<usize>)>,
    avoid_grouping: Vec<Vec<usize>>,
    ignore_groups: Vec<usize>,
}

fn create_data() -> Data {
    let table = BIOMES.parse::<Table>().unwrap();
    let mut names: Vec<String> = table["names"]
        .as_array()
        .unwrap()
        .iter()
        .map(|x| x.as_str().unwrap().to_string())
        .collect();
    names.sort();

    let mut props = Vec::new();

    for (name, values) in table["props"].as_table().unwrap().iter() {
        let mut v: Vec<usize> = values
            .as_array()
            .unwrap()
            .iter()
            .map(|x| {
                let name = x.as_str().unwrap();
                if let Ok(x) = names.binary_search_by_key(&name, |x| x) {
                    x
                } else {
                    panic!(r#"name "{}" not found"#, name);
                }
            })
            .collect();
        v.sort();
        props.push((name.clone(), v));
    }

    props.sort();

    let (avoid_grouping, ignore_groups) =
        if let Some(limits) = table.get("limits").map(|x| x.as_table().unwrap()) {
            let mut avoid_grouping: Vec<Vec<usize>> = limits
                .get("avoid-grouping")
                .unwrap()
                .as_array()
                .unwrap()
                .iter()
                .map(|x| {
                    let mut res: Vec<usize> = x
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|x| {
                            let name = x.as_str().unwrap();
                            if let Ok(x) = names.binary_search_by_key(&name, |x| x) {
                                x
                            } else {
                                panic!(r#"name "{}" not found"#, name);
                            }
                        })
                        .collect();
                    res.sort();
                    res
                })
                .collect();

            avoid_grouping.sort();

            let mut ignore_groups: Vec<usize> = limits
                .get("ignore-group")
                .unwrap()
                .as_array()
                .unwrap()
                .iter()
                .map(|x| {
                    let name = x.as_str().unwrap();
                    if let Ok(x) = props.binary_search_by_key(&name, |x| &x.0) {
                        x
                    } else {
                        panic!(r#"name "{}" not found"#, name);
                    }
                })
                .collect();

            ignore_groups.sort();

            (avoid_grouping, ignore_groups)
        } else {
            (Vec::new(), Vec::new())
        };

    Data {
        names,
        props,
        avoid_grouping,
        ignore_groups,
    }
}

fn exactly<'a, I: IntoIterator<Item = &'a Bool> + Clone>(args: I, k: u32) -> Bool {
    Bool::and(&[atleast(args.clone(), k), atmost(args, k)])
}

fn intersection(v1: &[usize], v2: &[usize]) -> Vec<usize> {
    debug_assert!(v1.is_sorted());
    debug_assert!(v2.is_sorted());
    let mut out = Vec::new();
    let mut i = 0;
    let mut j = 0;
    while i < v1.len() && j < v2.len() {
        match v1[i].cmp(&v2[j]) {
            std::cmp::Ordering::Less => i += 1,
            std::cmp::Ordering::Equal => {
                out.push(v1[i]);
                i += 1;
                j += 1;
            }
            std::cmp::Ordering::Greater => j += 1,
        }
    }
    out
}

fn main() {
    let data = create_data();

    let name_variables: Vec<Bool> = data.names.iter().map(|s| Bool::fresh_const(s)).collect();
    let group_variables: Vec<Bool> = data.props.iter().map(|s| Bool::fresh_const(&s.0)).collect();

    // For the ith name, which groups is it in
    let groups_of_names: Vec<Vec<&Bool>> = (0..data.names.len())
        .map(|i| {
            let mut out = Vec::new();
            for j in 0..data.props.len() {
                if data.props[j].1.contains(&i) {
                    out.push(&group_variables[j]);
                }
            }
            out
        })
        .collect();

    // Pairs of groups and all values in both groups
    let mut pairwise: Vec<(&Bool, &Bool, Vec<usize>)> = Vec::new();

    for i in 0..group_variables.len() {
        for j in 0..i {
            let name_i = &group_variables[i];
            let members_i = &data.props[i].1;
            let name_j = &group_variables[j];
            let members_j = &data.props[j].1;

            let inter = intersection(members_i, members_j);
            pairwise.push((name_i, name_j, inter));
        }
    }

    let solver = Solver::new();

    // Each name is in some group
    for i in 0..data.names.len() {
        let name_variable = &name_variables[i];
        let groups = &groups_of_names[i];
        solver.assert(name_variable.implies(Bool::or(groups)));
    }

    // If two groups are included and some element in their intersection, then there has to be four in their
    // intersection (which means that all are in their intersection).
    for (a, b, both) in pairwise {
        let inter_bool: Vec<&Bool> = both.iter().map(|&x| &name_variables[x]).collect();
        let some_inter = Bool::or(&inter_bool);
        let both_bool = Bool::and(&[a, b, &some_inter]);
        let has_four = exactly(both.iter().map(|&x| &name_variables[x]), 4);
        solver.assert(both_bool.implies(has_four));
    }

    // If we include a group, then we include exactly four of it's members
    for (i, group) in group_variables.iter().enumerate() {
        let members = &data.props[i].1;
        let has_four = exactly(members.iter().map(|&x| &name_variables[x]), 4);
        solver.assert(group.implies(has_four));
    }

    // Groups can't be active together with any pair of members that we're avoiding
    // grouping together.
    for (i, group) in group_variables.iter().enumerate() {
        let members = &data.props[i].1;
        for avoid in &data.avoid_grouping {
            let inter = intersection(members, avoid);
            for p in 0..inter.len() {
                for q in 0..p {
                    let a = inter[p];
                    let b = inter[q];
                    let bool_a = &name_variables[a];
                    let bool_b = &name_variables[b];
                    solver.assert(Bool::and(&[group, bool_a, bool_b]).not());
                }
            }
        }
    }

    // We don't choose a group that we're ignoring
    for ignored in data.ignore_groups {
        solver.assert(group_variables[ignored].not());
    }

    // We have 16 in total
    solver.assert(exactly(name_variables.iter(), 16));

    // let res = solver.check();
    // println!("{:?}", res);

    for (name_solution, group_solution) in solver
        .solutions((&name_variables, &group_variables), false)
        .take(10)
    {
        let values: Vec<bool> = group_solution
            .iter()
            .map(|x| x.as_bool().unwrap())
            .collect();
        let chosen_groups: Vec<usize> = data
            .props
            .iter()
            .enumerate()
            .filter(|(i, _)| values[*i])
            .map(|x| x.0)
            .collect();
        debug_assert!(chosen_groups.is_sorted());

        let values: Vec<bool> = name_solution.iter().map(|x| x.as_bool().unwrap()).collect();
        let chosen_names: Vec<usize> = data
            .names
            .iter()
            .enumerate()
            .filter(|(i, _)| values[*i])
            .map(|x| x.0)
            .collect();
        debug_assert!(chosen_names.is_sorted());

        println!("GROUPS: ");
        for i in &chosen_groups {
            let including = intersection(&chosen_names, &data.props[*i].1);
            let including_names: Vec<&String> = including.iter().map(|x| &data.names[*x]).collect();
            println!("{}: {:?} ", data.props[*i].0, including_names);
        }
    }
}
