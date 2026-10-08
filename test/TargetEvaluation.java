import java.nio.file.Files;
import java.nio.file.Path;
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
        for (int i = 2; i < args.length; i += 2) {
            var actual = engine.eval(args[i], "AgdaModel").strip();
            if (!args[i + 1].matches("true|false") ||
                !actual.matches("LiteralBoolean " + args[i + 1] + " \\([0-9a-f-]+\\)"))
                throw new AssertionError(args[i] + ": " + actual);
        }
    }
}
