// Complete translation of the declared required scope.
package 'AgdaModel' {
  private import ScalarValues::*;
  private import ControlFunctions::*;
  enum def 'Agda.Builtin.Equality._≡_<level 0, Register.State>.constructor-tag' {
    enum 'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>';
  }
  attribute def 'Agda.Builtin.Equality._≡_<level 0, Register.State>' {
    attribute redefines self : 'Agda.Builtin.Equality._≡_<level 0, Register.State>';
    assert constraint 'exact-type' { 'Agda.Builtin.Equality._≡_<level 0, Register.State>'::self hastype 'Agda.Builtin.Equality._≡_<level 0, Register.State>' }
    attribute 'constructor' : 'Agda.Builtin.Equality._≡_<level 0, Register.State>.constructor-tag' [1];
    attribute 'Agda.Builtin.Equality._≡_<level 0, Register.State>.index0' : 'Register.State' [1];
    attribute 'Agda.Builtin.Equality._≡_<level 0, Register.State>.index1' : 'Register.State' [1];
    attribute 'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>.payload0' : 'Register.State' [0..1];
    assert constraint 'valid-payload' { 'Agda.Builtin.Equality._≡_<level 0, Register.State>.payload-valid'('Agda.Builtin.Equality._≡_<level 0, Register.State>'::self) }
  }
  constraint def 'Agda.Builtin.Equality._≡_<level 0, Register.State>.payload-valid' {
    in 'value' : 'Agda.Builtin.Equality._≡_<level 0, Register.State>' [1];
    (SequenceFunctions::size('value'.'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>.payload0') == (if 'value'.'constructor' == 'Agda.Builtin.Equality._≡_<level 0, Register.State>.constructor-tag'::'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>' ? 1 else 0)) and (if 'value'.'constructor' == 'Agda.Builtin.Equality._≡_<level 0, Register.State>.constructor-tag'::'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>' ? ('value'.'Agda.Builtin.Equality._≡_<level 0, Register.State>.index0' == 'value'.'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>.payload0') else true) and (if 'value'.'constructor' == 'Agda.Builtin.Equality._≡_<level 0, Register.State>.constructor-tag'::'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>' ? ('value'.'Agda.Builtin.Equality._≡_<level 0, Register.State>.index1' == 'value'.'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>.payload0') else true)
  }
  enum def 'Register.Command.constructor-tag' {
    enum 'Register.Command.write';
    enum 'Register.Command.enable';
    enum 'Register.Command.replace';
    enum 'Register.Command.retain';
  }
  attribute def 'Register.Command' {
    attribute redefines self : 'Register.Command';
    assert constraint 'exact-type' { 'Register.Command'::self hastype 'Register.Command' }
    attribute 'constructor' : 'Register.Command.constructor-tag' [1];
    attribute 'Register.Command.write.payload0' : ScalarValues::Boolean [0..1];
    attribute 'Register.Command.enable.payload0' : ScalarValues::Boolean [0..1];
    attribute 'Register.Command.replace.payload0' : 'Register.State' [0..1];
    assert constraint 'valid-payload' { 'Register.Command.payload-valid'('Register.Command'::self) }
  }
  constraint def 'Register.Command.payload-valid' {
    in 'value' : 'Register.Command' [1];
    (SequenceFunctions::size('value'.'Register.Command.write.payload0') == (if 'value'.'constructor' == 'Register.Command.constructor-tag'::'Register.Command.write' ? 1 else 0)) and (SequenceFunctions::size('value'.'Register.Command.enable.payload0') == (if 'value'.'constructor' == 'Register.Command.constructor-tag'::'Register.Command.enable' ? 1 else 0)) and (SequenceFunctions::size('value'.'Register.Command.replace.payload0') == (if 'value'.'constructor' == 'Register.Command.constructor-tag'::'Register.Command.replace' ? 1 else 0))
  }
  attribute def 'Register.State' {
    attribute redefines self : 'Register.State';
    assert constraint 'exact-type' { 'Register.State'::self hastype 'Register.State' }
    attribute 'Register.State.value' : ScalarValues::Boolean [1];
    attribute 'Register.State.enabled' : ScalarValues::Boolean [1];
  }
  calc def 'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>' {
    in 'input0' : 'Register.State' [1];
    return 'result' : 'Agda.Builtin.Equality._≡_<level 0, Register.State>' [1] = new 'Agda.Builtin.Equality._≡_<level 0, Register.State>'('constructor' = 'Agda.Builtin.Equality._≡_<level 0, Register.State>.constructor-tag'::'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>', 'Agda.Builtin.Equality._≡_<level 0, Register.State>.index0' = 'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>'::'input0', 'Agda.Builtin.Equality._≡_<level 0, Register.State>.index1' = 'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>'::'input0', 'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>.payload0' = 'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>'::'input0');
    assert constraint 'index-contract-0' { ('Agda.Builtin.Equality._≡_.refl<level 0, Register.State>'::'result'.'Agda.Builtin.Equality._≡_<level 0, Register.State>.index0' == 'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>'::'input0') }
    assert constraint 'index-contract-1' { ('Agda.Builtin.Equality._≡_.refl<level 0, Register.State>'::'result'.'Agda.Builtin.Equality._≡_<level 0, Register.State>.index1' == 'Agda.Builtin.Equality._≡_.refl<level 0, Register.State>'::'input0') }
  }
  calc def 'Register.Command.enable' {
    in 'input0' : ScalarValues::Boolean [1];
    return 'result' : 'Register.Command' [1] = new 'Register.Command'('constructor' = 'Register.Command.constructor-tag'::'Register.Command.enable', 'Register.Command.write.payload0' = null, 'Register.Command.enable.payload0' = 'Register.Command.enable'::'input0', 'Register.Command.replace.payload0' = null);
  }
  calc def 'Register.Command.replace' {
    in 'input0' : 'Register.State' [1];
    return 'result' : 'Register.Command' [1] = new 'Register.Command'('constructor' = 'Register.Command.constructor-tag'::'Register.Command.replace', 'Register.Command.write.payload0' = null, 'Register.Command.enable.payload0' = null, 'Register.Command.replace.payload0' = 'Register.Command.replace'::'input0');
  }
  calc def 'Register.Command.retain' {
    return 'result' : 'Register.Command' [1] = new 'Register.Command'('constructor' = 'Register.Command.constructor-tag'::'Register.Command.retain', 'Register.Command.write.payload0' = null, 'Register.Command.enable.payload0' = null, 'Register.Command.replace.payload0' = null);
  }
  calc def 'Register.Command.write' {
    in 'input0' : ScalarValues::Boolean [1];
    return 'result' : 'Register.Command' [1] = new 'Register.Command'('constructor' = 'Register.Command.constructor-tag'::'Register.Command.write', 'Register.Command.write.payload0' = 'Register.Command.write'::'input0', 'Register.Command.enable.payload0' = null, 'Register.Command.replace.payload0' = null);
  }
  calc def 'Register.State.enabled' {
    in 'input0' : 'Register.State' [1];
    return 'result' : ScalarValues::Boolean [1] = ('Register.State.enabled'::'input0').'Register.State.enabled';
  }
  calc def 'Register.State.value' {
    in 'input0' : 'Register.State' [1];
    return 'result' : ScalarValues::Boolean [1] = ('Register.State.value'::'input0').'Register.State.value';
  }
  calc def 'Register.state' {
    in 'input0' : ScalarValues::Boolean [1];
    in 'input1' : ScalarValues::Boolean [1];
    return 'result' : 'Register.State' [1] = new 'Register.State'('Register.State.value' = 'Register.state'::'input0', 'Register.State.enabled' = 'Register.state'::'input1');
  }
  calc def 'Register.step' {
    in 'input0' : 'Register.Command' [1];
    in 'input1' : 'Register.State' [1];
    return 'result' : 'Register.State' [1] = (if (('Register.step'::'input0').'constructor' == 'Register.Command.constructor-tag'::'Register.Command.write') ? new 'Register.State'('Register.State.value' = ('Register.step'::'input0').'Register.Command.write.payload0', 'Register.State.enabled' = ('Register.step'::'input1').'Register.State.enabled') else (if (('Register.step'::'input0').'constructor' == 'Register.Command.constructor-tag'::'Register.Command.enable') ? new 'Register.State'('Register.State.value' = ('Register.step'::'input1').'Register.State.value', 'Register.State.enabled' = ('Register.step'::'input0').'Register.Command.enable.payload0') else (if (('Register.step'::'input0').'constructor' == 'Register.Command.constructor-tag'::'Register.Command.replace') ? ('Register.step'::'input0').'Register.Command.replace.payload0' else 'Register.step'::'input1')));
  }
  calc def 'RegisterWorkflow.sequence' {
    in 'input0' : 'Register.Command' [1];
    in 'input1' : 'Register.Command' [1];
    in 'input2' : 'Register.State' [1];
    return 'result' : 'Register.State' [1] = 'Register.step'('RegisterWorkflow.sequence'::'input1', 'Register.step'('RegisterWorkflow.sequence'::'input0', 'RegisterWorkflow.sequence'::'input2'));
  }
  constraint def 'RegisterWorkflow.replace-final.law' {
    in 'input0' : 'Register.Command' [1];
    in 'input1' : 'Register.State' [1];
    in 'input2' : 'Register.State' [1];
    ('RegisterWorkflow.sequence'('RegisterWorkflow.replace-final.law'::'input0', new 'Register.Command'('constructor' = 'Register.Command.constructor-tag'::'Register.Command.replace', 'Register.Command.write.payload0' = null, 'Register.Command.enable.payload0' = null, 'Register.Command.replace.payload0' = 'RegisterWorkflow.replace-final.law'::'input1'), 'RegisterWorkflow.replace-final.law'::'input2') == 'RegisterWorkflow.replace-final.law'::'input1')
  }
  constraint def 'RegisterWorkflow.retain-left.law' {
    in 'input0' : 'Register.Command' [1];
    in 'input1' : 'Register.State' [1];
    ('RegisterWorkflow.sequence'(new 'Register.Command'('constructor' = 'Register.Command.constructor-tag'::'Register.Command.retain', 'Register.Command.write.payload0' = null, 'Register.Command.enable.payload0' = null, 'Register.Command.replace.payload0' = null), 'RegisterWorkflow.retain-left.law'::'input0', 'RegisterWorkflow.retain-left.law'::'input1') == 'Register.step'('RegisterWorkflow.retain-left.law'::'input0', 'RegisterWorkflow.retain-left.law'::'input1'))
  }
  constraint def 'RegisterWorkflow.retain-right.law' {
    in 'input0' : 'Register.Command' [1];
    in 'input1' : 'Register.State' [1];
    ('RegisterWorkflow.sequence'('RegisterWorkflow.retain-right.law'::'input0', new 'Register.Command'('constructor' = 'Register.Command.constructor-tag'::'Register.Command.retain', 'Register.Command.write.payload0' = null, 'Register.Command.enable.payload0' = null, 'Register.Command.replace.payload0' = null), 'RegisterWorkflow.retain-right.law'::'input1') == 'Register.step'('RegisterWorkflow.retain-right.law'::'input0', 'RegisterWorkflow.retain-right.law'::'input1'))
  }
  constraint def 'RegisterWorkflow.sequence-associative.law' {
    in 'input0' : 'Register.Command' [1];
    in 'input1' : 'Register.Command' [1];
    in 'input2' : 'Register.Command' [1];
    in 'input3' : 'Register.State' [1];
    ('Register.step'('RegisterWorkflow.sequence-associative.law'::'input2', 'RegisterWorkflow.sequence'('RegisterWorkflow.sequence-associative.law'::'input0', 'RegisterWorkflow.sequence-associative.law'::'input1', 'RegisterWorkflow.sequence-associative.law'::'input3')) == 'RegisterWorkflow.sequence'('RegisterWorkflow.sequence-associative.law'::'input1', 'RegisterWorkflow.sequence-associative.law'::'input2', 'Register.step'('RegisterWorkflow.sequence-associative.law'::'input0', 'RegisterWorkflow.sequence-associative.law'::'input3')))
  }
}
