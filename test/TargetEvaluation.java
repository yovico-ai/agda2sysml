import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import org.omg.sysml.interactive.SysMLInteractive;

/** Execute emitted calculations with the independent, pinned target evaluator. */
public final class TargetEvaluation {
    public static void main(String[] args) throws Exception {
        if (args.length < 4 || args.length % 2 != 0) throw new IllegalArgumentException(
            "Expected library, model, and expression/Boolean pairs");
        var engine = SysMLInteractive.createInstance();
        engine.setVerbose(false);
        engine.loadLibrary(args[0]);
        var checked = engine.process(Files.readString(Path.of(args[1])));
        if (checked.hasErrors() || checked.getException() != null)
            throw new IllegalStateException(checked.formatIssues());
        var failures = new ArrayList<String>();
        for (int i = 2; i < args.length; i += 2) {
            try {
                var actual = engine.eval(args[i], "AgdaModel").strip();
                if (!args[i + 1].matches("true|false") ||
                    !actual.matches("LiteralBoolean " + args[i + 1] + " \\([0-9a-f-]+\\)"))
                    failures.add(args[i] + ": expected " + args[i + 1] + "; actual " + actual);
            } catch (Exception error) {
                failures.add(args[i] + ": " + error);
            }
        }
        System.out.println("Target evaluation: " + ((args.length - 2) / 2 - failures.size())
            + " passed, " + failures.size() + " failed");
        for (var failure : failures) System.err.println(failure);
        if (!failures.isEmpty())
            throw new AssertionError("Target evaluation failed for " + failures.size() + " expressions");
    }
}
