module algebraic;

import std.meta, std.traits;
version (unittest) import std.format;

/** Algebraic data type.

Params:
Args = the list of tags preceded by the (optional) argument types of the tags.

Bugs:
Self-referential types are not supported.

Examples:
In Haskell, Maybe is defined as data Maybe a = Nothing | Just a.
This is achieved by:
---
alias Maybe!A = Algebraic!("Nothing", A, "Just");
---
*/
template Algebraic(Args...)
{
    alias children = parseSpecs!Args;
    mixin (concatStrings!(
        "Algebraic".generateBaseClassDeclaration!children,
        staticMap!(ExtractClassDefinition, children)
        ));
}

///
unittest
{
    // declaration
    alias MaybeIndex = Algebraic!("Nothing", size_t, "Just");

    // as function return type
    static MaybeIndex find(E)(E[] haystack, E needle)
    {
        foreach (i, h; haystack)
            if (h == needle)
                return MaybeIndex.just(i);
        return MaybeIndex.nothing;
    }

    // function argument type (see below)
    alias f = algebraicFunc!(
        (MaybeIndex.Just j) => "found: %s-th".format(j.x0),
        (MaybeIndex.Nothing n) => "not found");

    // search and process result
    assert (f(find([1, 2, 3], 1)) == "found: 0-th");
    assert (f(find([1, 2, 3], 0)) == "not found");
}
/** (Very simple) pattern match function.

Params:
Functions = functions each of which take a value of a subtype of an instanciation of Algebraic.
x = a value of the instanciation of Algebraic.
*/
CommonType!(staticMap!(ReturnType, Functions)) algebraicFunc(Functions...)(CommonType!(staticMap!(Parameters, Functions)) x)
    if (is (CommonType!(staticMap!(Parameters, Functions)) : Algebraic!AlgebraicArgs, AlgebraicArgs...))
{
    foreach (f; Functions)
    {
        if (auto p = cast(Parameters!f[0])x)
            return f(p);
    }
    assert (false, "non-exhaustive patterns!");
}
enum ExtractClassDefinition(alias Child) = Child.classDefinition;
template concatStrings(Args...)
{
    static if (Args.length)
        enum concatStrings = Args[0] ~ "\n" ~ concatStrings!(Args[1..$]);
    else
        enum concatStrings = "";
}
template parseSpecs(Specs...)
{
    static if (Specs.length == 0)
        alias parseSpecs = AliasSeq!();
    else
    {
        enum size_t numarg = StaticFindValue!(string, Specs);
        alias parseSpecs = AliasSeq!(
            ChildSpec!(Specs[numarg], Specs[0..numarg]),
            parseSpecs!(Specs[numarg+1..$]));
    }
}
template ChildSpec(string name, Args...)
{
    import std.ascii;
    enum className = name[0].toUpper ~ name[1..$];
    enum ctorName = name[0].toLower ~ name[1..$];
    alias MemberTypes = Args;
    enum classDefinition = name.generateClassDeclaration!Args("Algebraic");
}
template StaticFindValue(T, Args...)
{
    static assert (Args.length);
    static if (is (typeof (Args[0]) : T))
        enum size_t StaticFindValue = 0;
    else
        enum size_t StaticFindValue = StaticFindValue!(T, Args[1..$]) + 1;
}
auto generateClassDeclaration(Members...)(string className, string parentName)
{
    import std.array, std.format;
    auto ret = appender!string;
    ret.put("class _"~className~" : "~parentName);
    {
        ret.put("{"); scope (exit) ret.put("}");
        foreach (i, MemberType; Members)
            ret.put("%s x%d;".format(MemberType.stringof, i));
        {
            ret.put("this ("); scope (exit) ret.put(")");
            string sep = "";
            foreach (i, MemberType; Members)
            {
                ret.put("%s%s x%d".format(sep, MemberType.stringof, i));
                sep = ", ";
            }
        }
        {
            ret.put("{"); scope (exit) ret.put("}");
            foreach (i, MemberType; Members)
            {
                ret.put("this.x%1$s = x%1$s;".format(i));
            }
        }
        ret.put("static bool equal(%1$s lhs, %1$s rhs)".format(parentName));
        {
            ret.put("{"); scope (exit) ret.put("}");
            ret.put("if (auto l = cast(%1$s) lhs)
                     if (auto r = cast(%1$s) rhs)".format(className));
            {
                ret.put("{"); scope (exit) ret.put("}");
                foreach (i, MemberType; Members)
                {
                    ret.put("if (l.x%1$s != r.x%1$s) return false;".format(i));
                }
                ret.put("return true;");
            }
            ret.put("return false;");
        }
    }
    return ret.data;
}
auto generateBaseClassDeclaration(Children...)(string className)
{
    import std.array, std.format;
    auto ret = appender!string;
    ret.put("abstract class "~className);
    {
        ret.put("{"); scope (exit) ret.put("}");
        foreach (Child; Children)
        {
            ret.put("alias %s = _%s;".format(Child.className, Child.className));
            ret.put("static %s %s".format(Child.className, Child.ctorName));
            {
                ret.put("("); scope (exit) ret.put(")");
                string sep = "";
                foreach (i, MemberType; Child.MemberTypes)
                {
                    ret.put("%s%s x%d".format(sep, MemberType.stringof, i));
                    sep = ", ";
                }
            }
            {
                ret.put("{"); scope (exit) ret.put("}");
                ret.put("return new %s".format(Child.className));
                scope (exit) ret.put(";");
                {
                    ret.put("("); scope (exit) ret.put(")");
                    string sep = "";
                    foreach (i, MemberType; Child.MemberTypes)
                    {
                        ret.put("%sx%d".format(sep, i));
                        sep = ", ";
                    }
                }
            }
        }
        ret.put("override bool opEquals(Object rhs)");
        {
            ret.put("{"); scope (exit) ret.put("}");
            ret.put("auto r = cast(%s)rhs;".format(className));
            ret.put("if (r is null) return false;");
            foreach (Child; Children)
                ret.put("if (%1$s.equal(this, r)) return true;".format(Child.className));
            ret.put("return false;");
        }
    }
    return ret.data;
}
